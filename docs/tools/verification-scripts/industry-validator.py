#!/usr/bin/env python3
"""
行业验证器
用于验证各行业模型与标准的一致性
"""

import json
import yaml
from typing import Dict, Any, List, Optional, Tuple
from dataclasses import dataclass
from pathlib import Path
import logging
from datetime import datetime

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

@dataclass
class ValidationResult:
    """验证结果"""
    industry: str
    model_type: str
    validation_status: str  # "passed", "failed", "warning"
    issues: List[str]
    recommendations: List[str]
    validated_at: datetime

class IndustryValidator:
    """行业验证器"""
    
    def __init__(self, models_dir: str = "docs/models", evidence_dir: str = "docs/evidence"):
        self.models_dir = Path(models_dir)
        self.evidence_dir = Path(evidence_dir)
        self.validation_results = []
    
    def validate_cloud_native_models(self) -> ValidationResult:
        """验证云原生模型"""
        issues = []
        recommendations = []
        
        # 检查Kubernetes相关模型
        k8s_models = [
            "runtime-model",
            "deployment-model", 
            "monitoring-model",
            "control-scheduling-model"
        ]
        
        for model in k8s_models:
            model_path = self.models_dir / "meta-models" / f"{model}" / "README.md"
            if not model_path.exists():
                issues.append(f"缺少 {model} 元模型文档")
            else:
                # 检查模型内容是否包含Kubernetes相关概念
                content = model_path.read_text(encoding='utf-8')
                if "kubernetes" not in content.lower() and "k8s" not in content.lower():
                    issues.append(f"{model} 模型缺少Kubernetes相关概念")
        
        # 检查标准模型实现
        standard_models = [
            "runtime-standard-model.md",
            "deployment-standard-model.md",
            "monitoring-standard-model.md"
        ]
        
        for model_file in standard_models:
            model_path = self.models_dir / "standard-models" / model_file
            if not model_path.exists():
                issues.append(f"缺少标准模型: {model_file}")
            else:
                # 验证标准模型内容
                content = model_path.read_text(encoding='utf-8')
                if "container" not in content.lower():
                    issues.append(f"{model_file} 缺少容器相关实现")
        
        # 检查证据条目
        evidence_file = self.evidence_dir / "EVIDENCE_CLOUD_NATIVE.md"
        if not evidence_file.exists():
            issues.append("缺少云原生行业证据文档")
        else:
            evidence_content = evidence_file.read_text(encoding='utf-8')
            if "K8S-001" not in evidence_content:
                issues.append("缺少Kubernetes容器编排证据")
        
        # 生成建议
        if not issues:
            recommendations.append("云原生模型验证通过，建议增加更多微服务架构相关模型")
        else:
            recommendations.append("完善缺失的模型文档和证据条目")
            recommendations.append("增加容器编排和微服务治理相关标准")
        
        status = "passed" if not issues else "failed"
        
        return ValidationResult(
            industry="cloud_native",
            model_type="meta_models_and_standard_models",
            validation_status=status,
            issues=issues,
            recommendations=recommendations,
            validated_at=datetime.now()
        )
    
    def validate_finance_models(self) -> ValidationResult:
        """验证金融模型"""
        issues = []
        recommendations = []
        
        # 检查金融特定模型
        finance_models = [
            "interaction-model",  # API交互
            "data-model",         # 数据安全
            "monitoring-model",   # 合规监控
            "testing-model"       # 安全测试
        ]
        
        for model in finance_models:
            model_path = self.models_dir / "meta-models" / f"{model}" / "README.md"
            if not model_path.exists():
                issues.append(f"缺少 {model} 元模型文档")
            else:
                content = model_path.read_text(encoding='utf-8')
                # 检查是否包含金融相关概念
                finance_keywords = ["security", "compliance", "audit", "encryption", "pci"]
                if not any(keyword in content.lower() for keyword in finance_keywords):
                    issues.append(f"{model} 模型缺少金融安全相关概念")
        
        # 检查标准模型
        standard_models = [
            "interaction-standard-model.md",
            "data-standard-model.md"
        ]
        
        for model_file in standard_models:
            model_path = self.models_dir / "standard-models" / model_file
            if not model_path.exists():
                issues.append(f"缺少标准模型: {model_file}")
            else:
                content = model_path.read_text(encoding='utf-8')
                if "authentication" not in content.lower() and "authorization" not in content.lower():
                    issues.append(f"{model_file} 缺少认证授权相关实现")
        
        # 检查证据条目
        evidence_file = self.evidence_dir / "EVIDENCE_FINANCE.md"
        if not evidence_file.exists():
            issues.append("缺少金融行业证据文档")
        else:
            evidence_content = evidence_file.read_text(encoding='utf-8')
            if "FIN-API-001" not in evidence_content:
                issues.append("缺少开放银行API证据")
            if "FIN-PCI-001" not in evidence_content:
                issues.append("缺少PCI DSS合规证据")
        
        # 生成建议
        if not issues:
            recommendations.append("金融模型验证通过，建议增加更多合规性检查标准")
        else:
            recommendations.append("完善金融安全相关模型")
            recommendations.append("增加PCI DSS和SOX合规性标准")
            recommendations.append("完善API安全认证机制")
        
        status = "passed" if not issues else "failed"
        
        return ValidationResult(
            industry="finance",
            model_type="meta_models_and_standard_models",
            validation_status=status,
            issues=issues,
            recommendations=recommendations,
            validated_at=datetime.now()
        )
    
    def validate_iot_models(self) -> ValidationResult:
        """验证IoT模型"""
        issues = []
        recommendations = []
        
        # 检查IoT特定模型
        iot_models = [
            "interaction-model",  # 设备通信
            "data-model",         # 时序数据
            "monitoring-model",   # 设备监控
            "deployment-model"    # 边缘部署
        ]
        
        for model in iot_models:
            model_path = self.models_dir / "meta-models" / f"{model}" / "README.md"
            if not model_path.exists():
                issues.append(f"缺少 {model} 元模型文档")
            else:
                content = model_path.read_text(encoding='utf-8')
                # 检查是否包含IoT相关概念
                iot_keywords = ["device", "sensor", "mqtt", "edge", "timeseries"]
                if not any(keyword in content.lower() for keyword in iot_keywords):
                    issues.append(f"{model} 模型缺少IoT相关概念")
        
        # 检查标准模型
        standard_models = [
            "interaction-standard-model.md",
            "data-standard-model.md"
        ]
        
        for model_file in standard_models:
            model_path = self.models_dir / "standard-models" / model_file
            if not model_path.exists():
                issues.append(f"缺少标准模型: {model_file}")
            else:
                content = model_path.read_text(encoding='utf-8')
                if "mqtt" not in content.lower() and "coap" not in content.lower():
                    issues.append(f"{model_file} 缺少IoT通信协议实现")
        
        # 检查证据条目
        evidence_file = self.evidence_dir / "EVIDENCE_IOT.md"
        if not evidence_file.exists():
            issues.append("缺少IoT行业证据文档")
        else:
            evidence_content = evidence_file.read_text(encoding='utf-8')
            if "IOT-001" not in evidence_content:
                issues.append("缺少设备管理证据")
            if "IOT-002" not in evidence_content:
                issues.append("缺少MQTT协议证据")
        
        # 生成建议
        if not issues:
            recommendations.append("IoT模型验证通过，建议增加更多边缘计算相关模型")
        else:
            recommendations.append("完善IoT设备管理相关模型")
            recommendations.append("增加时序数据处理标准")
            recommendations.append("完善边缘计算部署模型")
        
        status = "passed" if not issues else "failed"
        
        return ValidationResult(
            industry="iot",
            model_type="meta_models_and_standard_models",
            validation_status=status,
            issues=issues,
            recommendations=recommendations,
            validated_at=datetime.now()
        )
    
    def validate_ai_models(self) -> ValidationResult:
        """验证AI模型"""
        issues = []
        recommendations = []
        
        # 检查AI特定模型
        ai_models = [
            "runtime-model",      # 模型推理
            "data-model",         # 训练数据
            "monitoring-model",   # 模型监控
            "deployment-model"    # 模型部署
        ]
        
        for model in ai_models:
            model_path = self.models_dir / "meta-models" / f"{model}" / "README.md"
            if not model_path.exists():
                issues.append(f"缺少 {model} 元模型文档")
            else:
                content = model_path.read_text(encoding='utf-8')
                # 检查是否包含AI相关概念
                ai_keywords = ["model", "training", "inference", "mlops", "pipeline"]
                if not any(keyword in content.lower() for keyword in ai_keywords):
                    issues.append(f"{model} 模型缺少AI相关概念")
        
        # 检查标准模型
        standard_models = [
            "runtime-standard-model.md",
            "data-standard-model.md"
        ]
        
        for model_file in standard_models:
            model_path = self.models_dir / "standard-models" / model_file
            if not model_path.exists():
                issues.append(f"缺少标准模型: {model_file}")
            else:
                content = model_path.read_text(encoding='utf-8')
                if "tensorflow" not in content.lower() and "pytorch" not in content.lower():
                    issues.append(f"{model_file} 缺少AI框架相关实现")
        
        # 检查证据条目
        evidence_file = self.evidence_dir / "EVIDENCE_AI.md"
        if not evidence_file.exists():
            issues.append("缺少AI行业证据文档")
        else:
            evidence_content = evidence_file.read_text(encoding='utf-8')
            if "AI-001" not in evidence_content:
                issues.append("缺少模型训练证据")
            if "AI-002" not in evidence_content:
                issues.append("缺少模型推理证据")
        
        # 生成建议
        if not issues:
            recommendations.append("AI模型验证通过，建议增加更多MLOps相关模型")
        else:
            recommendations.append("完善AI模型训练和推理相关模型")
            recommendations.append("增加MLOps流水线标准")
            recommendations.append("完善模型版本管理机制")
        
        status = "passed" if not issues else "failed"
        
        return ValidationResult(
            industry="ai",
            model_type="meta_models_and_standard_models",
            validation_status=status,
            issues=issues,
            recommendations=recommendations,
            validated_at=datetime.now()
        )
    
    def validate_web3_models(self) -> ValidationResult:
        """验证Web3模型"""
        issues = []
        recommendations = []
        
        # 检查Web3特定模型
        web3_models = [
            "interaction-model",  # 智能合约交互
            "data-model",         # 区块链数据
            "monitoring-model",   # 链上监控
            "deployment-model"    # 合约部署
        ]
        
        for model in web3_models:
            model_path = self.models_dir / "meta-models" / f"{model}" / "README.md"
            if not model_path.exists():
                issues.append(f"缺少 {model} 元模型文档")
            else:
                content = model_path.read_text(encoding='utf-8')
                # 检查是否包含Web3相关概念
                web3_keywords = ["blockchain", "smart_contract", "decentralized", "consensus"]
                if not any(keyword in content.lower() for keyword in web3_keywords):
                    issues.append(f"{model} 模型缺少Web3相关概念")
        
        # 检查标准模型
        standard_models = [
            "interaction-standard-model.md",
            "data-standard-model.md"
        ]
        
        for model_file in standard_models:
            model_path = self.models_dir / "standard-models" / model_file
            if not model_path.exists():
                issues.append(f"缺少标准模型: {model_file}")
            else:
                content = model_path.read_text(encoding='utf-8')
                if "ethereum" not in content.lower() and "solidity" not in content.lower():
                    issues.append(f"{model_file} 缺少区块链相关实现")
        
        # 检查证据条目
        evidence_file = self.evidence_dir / "EVIDENCE_WEB3.md"
        if not evidence_file.exists():
            issues.append("缺少Web3行业证据文档")
        else:
            evidence_content = evidence_file.read_text(encoding='utf-8')
            if "W3-001" not in evidence_content:
                issues.append("缺少智能合约证据")
            if "W3-002" not in evidence_content:
                issues.append("缺少去中心化存储证据")
        
        # 生成建议
        if not issues:
            recommendations.append("Web3模型验证通过，建议增加更多DeFi相关模型")
        else:
            recommendations.append("完善区块链和智能合约相关模型")
            recommendations.append("增加去中心化存储标准")
            recommendations.append("完善跨链互操作机制")
        
        status = "passed" if not issues else "failed"
        
        return ValidationResult(
            industry="web3",
            model_type="meta_models_and_standard_models",
            validation_status=status,
            issues=issues,
            recommendations=recommendations,
            validated_at=datetime.now()
        )
    
    def validate_all_industries(self) -> List[ValidationResult]:
        """验证所有行业模型"""
        logger.info("开始验证所有行业模型...")
        
        validators = {
            "cloud_native": self.validate_cloud_native_models,
            "finance": self.validate_finance_models,
            "iot": self.validate_iot_models,
            "ai": self.validate_ai_models,
            "web3": self.validate_web3_models
        }
        
        results = []
        for industry, validator_func in validators.items():
            logger.info(f"验证 {industry} 行业模型...")
            result = validator_func()
            results.append(result)
            self.validation_results.append(result)
            
            logger.info(f"{industry} 验证完成: {result.validation_status}")
        
        return results
    
    def generate_validation_report(self, results: List[ValidationResult]):
        """生成验证报告"""
        report_file = Path("validation-report.md")
        
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write("# 行业模型验证报告\n\n")
            f.write(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            
            # 总体统计
            total_industries = len(results)
            passed_industries = sum(1 for r in results if r.validation_status == "passed")
            failed_industries = sum(1 for r in results if r.validation_status == "failed")
            
            f.write("## 总体统计\n\n")
            f.write(f"- 总行业数: {total_industries}\n")
            f.write(f"- 验证通过: {passed_industries}\n")
            f.write(f"- 验证失败: {failed_industries}\n")
            f.write(f"- 通过率: {passed_industries/total_industries*100:.1f}%\n\n")
            
            # 详细结果
            f.write("## 详细验证结果\n\n")
            for result in results:
                f.write(f"### {result.industry.upper()} 行业\n\n")
                f.write(f"**验证状态**: {result.validation_status}\n\n")
                f.write(f"**验证时间**: {result.validated_at.strftime('%Y-%m-%d %H:%M:%S')}\n\n")
                
                if result.issues:
                    f.write("**问题列表**:\n")
                    for issue in result.issues:
                        f.write(f"- {issue}\n")
                    f.write("\n")
                
                if result.recommendations:
                    f.write("**改进建议**:\n")
                    for rec in result.recommendations:
                        f.write(f"- {rec}\n")
                    f.write("\n")
                
                f.write("---\n\n")
            
            # 优先级建议
            f.write("## 优先级改进建议\n\n")
            failed_results = [r for r in results if r.validation_status == "failed"]
            if failed_results:
                f.write("### 高优先级（验证失败）\n\n")
                for result in failed_results:
                    f.write(f"- **{result.industry.upper()}**: 需要立即修复 {len(result.issues)} 个问题\n")
                f.write("\n")
            
            passed_results = [r for r in results if r.validation_status == "passed"]
            if passed_results:
                f.write("### 中优先级（验证通过但可优化）\n\n")
                for result in passed_results:
                    f.write(f"- **{result.industry.upper()}**: 可考虑实施 {len(result.recommendations)} 项改进建议\n")
                f.write("\n")
    
    def export_validation_results(self, results: List[ValidationResult]):
        """导出验证结果为JSON"""
        json_file = Path("validation-results.json")
        
        results_data = []
        for result in results:
            result_dict = {
                "industry": result.industry,
                "model_type": result.model_type,
                "validation_status": result.validation_status,
                "issues": result.issues,
                "recommendations": result.recommendations,
                "validated_at": result.validated_at.isoformat()
            }
            results_data.append(result_dict)
        
        with open(json_file, 'w', encoding='utf-8') as f:
            json.dump(results_data, f, indent=2, ensure_ascii=False)

def main():
    """主函数"""
    validator = IndustryValidator()
    results = validator.validate_all_industries()
    validator.generate_validation_report(results)
    validator.export_validation_results(results)
    
    logger.info("行业模型验证完成")

if __name__ == "__main__":
    main()
