#!/usr/bin/env python3
"""
CI/CD流水线自动化脚本
用于自动化构建、测试、部署流程
"""

import os
import sys
import json
import yaml
import subprocess
import time
from typing import Dict, Any, List, Optional
from dataclasses import dataclass
from pathlib import Path
import logging
from datetime import datetime
import requests

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

@dataclass
class PipelineStage:
    """流水线阶段"""
    name: str
    status: str  # "pending", "running", "success", "failed", "skipped"
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None
    duration: Optional[float] = None
    output: str = ""
    error: str = ""

@dataclass
class PipelineResult:
    """流水线结果"""
    pipeline_id: str
    status: str  # "success", "failed", "cancelled"
    stages: List[PipelineStage]
    start_time: datetime
    end_time: Optional[datetime] = None
    total_duration: Optional[float] = None

class CICDPipeline:
    """CI/CD流水线"""
    
    def __init__(self, config_file: str = "docs/tools/automation/ci-cd-config.yaml"):
        self.config_file = Path(config_file)
        self.config = self._load_config()
        self.pipeline_id = f"pipeline-{int(time.time())}"
        self.stages = []
        self.current_stage = None
    
    def _load_config(self) -> Dict[str, Any]:
        """加载配置文件"""
        if self.config_file.exists():
            with open(self.config_file, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        else:
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            "pipeline": {
                "name": "formal-framework-ci-cd",
                "stages": [
                    {
                        "name": "checkout",
                        "commands": ["git fetch", "git checkout main"]
                    },
                    {
                        "name": "install_dependencies",
                        "commands": ["pip install -r requirements.txt"]
                    },
                    {
                        "name": "lint",
                        "commands": ["python -m flake8 .", "python -m black --check ."]
                    },
                    {
                        "name": "test",
                        "commands": ["python -m pytest tests/ -v"]
                    },
                    {
                        "name": "build",
                        "commands": ["python setup.py build"]
                    },
                    {
                        "name": "security_scan",
                        "commands": ["python -m bandit -r ."]
                    },
                    {
                        "name": "deploy_staging",
                        "commands": ["python deploy.py --env staging"],
                        "manual_trigger": True
                    },
                    {
                        "name": "deploy_production",
                        "commands": ["python deploy.py --env production"],
                        "manual_trigger": True,
                        "approval_required": True
                    }
                ]
            },
            "notifications": {
                "slack_webhook": None,
                "email_recipients": []
            }
        }
    
    def run_stage(self, stage_config: Dict[str, Any]) -> PipelineStage:
        """运行流水线阶段"""
        stage_name = stage_config["name"]
        commands = stage_config.get("commands", [])
        manual_trigger = stage_config.get("manual_trigger", False)
        approval_required = stage_config.get("approval_required", False)
        
        logger.info(f"开始执行阶段: {stage_name}")
        
        stage = PipelineStage(
            name=stage_name,
            status="running",
            start_time=datetime.now()
        )
        
        # 检查是否需要手动触发
        if manual_trigger:
            if not self._is_manual_triggered(stage_name):
                stage.status = "skipped"
                stage.output = "手动触发阶段，未触发"
                logger.info(f"跳过手动触发阶段: {stage_name}")
                return stage
        
        # 检查是否需要审批
        if approval_required:
            if not self._is_approved(stage_name):
                stage.status = "failed"
                stage.error = "需要审批但未获得审批"
                logger.error(f"阶段 {stage_name} 需要审批但未获得审批")
                return stage
        
        # 执行命令
        try:
            for command in commands:
                logger.info(f"执行命令: {command}")
                result = subprocess.run(
                    command,
                    shell=True,
                    capture_output=True,
                    text=True,
                    cwd=Path.cwd()
                )
                
                stage.output += f"命令: {command}\n"
                stage.output += f"返回码: {result.returncode}\n"
                stage.output += f"输出: {result.stdout}\n"
                
                if result.stderr:
                    stage.output += f"错误: {result.stderr}\n"
                
                if result.returncode != 0:
                    stage.status = "failed"
                    stage.error = f"命令执行失败: {command}"
                    stage.end_time = datetime.now()
                    stage.duration = (stage.end_time - stage.start_time).total_seconds()
                    logger.error(f"阶段 {stage_name} 执行失败: {stage.error}")
                    return stage
            
            stage.status = "success"
            stage.end_time = datetime.now()
            stage.duration = (stage.end_time - stage.start_time).total_seconds()
            logger.info(f"阶段 {stage_name} 执行成功，耗时: {stage.duration:.2f}秒")
            
        except Exception as e:
            stage.status = "failed"
            stage.error = str(e)
            stage.end_time = datetime.now()
            stage.duration = (stage.end_time - stage.start_time).total_seconds()
            logger.error(f"阶段 {stage_name} 执行异常: {e}")
        
        return stage
    
    def _is_manual_triggered(self, stage_name: str) -> bool:
        """检查是否手动触发"""
        # 这里应该检查实际的触发条件
        # 可以通过环境变量、配置文件或API调用
        return os.getenv(f"TRIGGER_{stage_name.upper()}", "false").lower() == "true"
    
    def _is_approved(self, stage_name: str) -> bool:
        """检查是否已审批"""
        # 这里应该检查实际的审批状态
        # 可以通过API调用或检查审批文件
        return os.getenv(f"APPROVED_{stage_name.upper()}", "false").lower() == "true"
    
    def run_pipeline(self) -> PipelineResult:
        """运行完整流水线"""
        logger.info(f"开始运行流水线: {self.pipeline_id}")
        
        start_time = datetime.now()
        stages = []
        
        pipeline_config = self.config["pipeline"]
        stage_configs = pipeline_config.get("stages", [])
        
        for stage_config in stage_configs:
            stage = self.run_stage(stage_config)
            stages.append(stage)
            
            # 如果阶段失败，停止流水线
            if stage.status == "failed":
                logger.error(f"流水线在阶段 {stage.name} 失败，停止执行")
                break
        
        end_time = datetime.now()
        total_duration = (end_time - start_time).total_seconds()
        
        # 计算总体状态
        failed_stages = [s for s in stages if s.status == "failed"]
        if failed_stages:
            overall_status = "failed"
        else:
            overall_status = "success"
        
        result = PipelineResult(
            pipeline_id=self.pipeline_id,
            status=overall_status,
            stages=stages,
            start_time=start_time,
            end_time=end_time,
            total_duration=total_duration
        )
        
        self.stages = stages
        
        logger.info(f"流水线执行完成，状态: {overall_status}，总耗时: {total_duration:.2f}秒")
        return result
    
    def generate_report(self, result: PipelineResult) -> str:
        """生成流水线报告"""
        report_lines = [
            "# CI/CD流水线报告",
            f"流水线ID: {result.pipeline_id}",
            f"开始时间: {result.start_time.strftime('%Y-%m-%d %H:%M:%S')}",
            f"结束时间: {result.end_time.strftime('%Y-%m-%d %H:%M:%S') if result.end_time else 'N/A'}",
            f"总耗时: {result.total_duration:.2f}秒" if result.total_duration else "总耗时: N/A",
            f"总体状态: {result.status}",
            "",
            "## 阶段详情",
            ""
        ]
        
        for stage in result.stages:
            status_emoji = {
                "success": "✅",
                "failed": "❌",
                "skipped": "⏭️",
                "running": "🔄",
                "pending": "⏳"
            }.get(stage.status, "❓")
            
            report_lines.extend([
                f"### {status_emoji} {stage.name}",
                f"**状态**: {stage.status}",
                f"**开始时间**: {stage.start_time.strftime('%Y-%m-%d %H:%M:%S') if stage.start_time else 'N/A'}",
                f"**结束时间**: {stage.end_time.strftime('%Y-%m-%d %H:%M:%S') if stage.end_time else 'N/A'}",
                f"**耗时**: {stage.duration:.2f}秒" if stage.duration else "**耗时**: N/A",
                ""
            ])
            
            if stage.output:
                report_lines.extend([
                    "**输出**:",
                    "```",
                    stage.output,
                    "```",
                    ""
                ])
            
            if stage.error:
                report_lines.extend([
                    "**错误**:",
                    "```",
                    stage.error,
                    "```",
                    ""
                ])
        
        return "\n".join(report_lines)
    
    def send_notifications(self, result: PipelineResult):
        """发送通知"""
        # Slack通知
        slack_webhook = self.config.get("notifications", {}).get("slack_webhook")
        if slack_webhook:
            self._send_slack_notification(result)
        
        # 邮件通知
        email_recipients = self.config.get("notifications", {}).get("email_recipients", [])
        if email_recipients:
            self._send_email_notification(result)
    
    def _send_slack_notification(self, result: PipelineResult):
        """发送Slack通知"""
        try:
            slack_webhook = self.config["notifications"]["slack_webhook"]
            
            status_emoji = "✅" if result.status == "success" else "❌"
            message = f"{status_emoji} CI/CD流水线执行完成\n"
            message += f"流水线ID: {result.pipeline_id}\n"
            message += f"状态: {result.status}\n"
            message += f"耗时: {result.total_duration:.2f}秒\n"
            
            if result.status == "failed":
                failed_stages = [s.name for s in result.stages if s.status == "failed"]
                message += f"失败阶段: {', '.join(failed_stages)}\n"
            
            payload = {"text": message}
            response = requests.post(slack_webhook, json=payload)
            
            if response.status_code == 200:
                logger.info("Slack通知发送成功")
            else:
                logger.error(f"Slack通知发送失败: {response.status_code}")
        except Exception as e:
            logger.error(f"Slack通知发送异常: {e}")
    
    def _send_email_notification(self, result: PipelineResult):
        """发送邮件通知"""
        # 这里应该实现邮件发送逻辑
        logger.info("邮件通知功能待实现")
    
    def save_artifacts(self, result: PipelineResult):
        """保存构建产物"""
        artifacts_dir = Path("artifacts")
        artifacts_dir.mkdir(exist_ok=True)
        
        # 保存流水线报告
        report_content = self.generate_report(result)
        report_file = artifacts_dir / f"pipeline-report-{result.pipeline_id}.md"
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write(report_content)
        
        # 保存流水线结果JSON
        result_data = {
            "pipeline_id": result.pipeline_id,
            "status": result.status,
            "start_time": result.start_time.isoformat(),
            "end_time": result.end_time.isoformat() if result.end_time else None,
            "total_duration": result.total_duration,
            "stages": [
                {
                    "name": stage.name,
                    "status": stage.status,
                    "start_time": stage.start_time.isoformat() if stage.start_time else None,
                    "end_time": stage.end_time.isoformat() if stage.end_time else None,
                    "duration": stage.duration,
                    "output": stage.output,
                    "error": stage.error
                }
                for stage in result.stages
            ]
        }
        
        result_file = artifacts_dir / f"pipeline-result-{result.pipeline_id}.json"
        with open(result_file, 'w', encoding='utf-8') as f:
            json.dump(result_data, f, indent=2, ensure_ascii=False)
        
        logger.info(f"构建产物已保存到 {artifacts_dir}")

def main():
    """主函数"""
    pipeline = CICDPipeline()
    result = pipeline.run_pipeline()
    
    # 生成报告
    report_content = pipeline.generate_report(result)
    print(report_content)
    
    # 保存产物
    pipeline.save_artifacts(result)
    
    # 发送通知
    pipeline.send_notifications(result)
    
    # 根据结果设置退出码
    if result.status == "failed":
        sys.exit(1)
    else:
        sys.exit(0)

if __name__ == "__main__":
    main()
