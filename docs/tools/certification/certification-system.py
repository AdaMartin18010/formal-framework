#!/usr/bin/env python3
"""
正式验证框架认证体系
提供四级认证：基础、进阶、专家、大师
"""

import json
import hashlib
import datetime
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, asdict
from enum import Enum


class CertificationLevel(Enum):
    """认证等级"""
    FOUNDATION = "foundation"      # 基础认证
    INTERMEDIATE = "intermediate"  # 进阶认证
    EXPERT = "expert"             # 专家认证
    MASTER = "master"             # 大师认证


@dataclass
class CertificationRequirement:
    """认证要求"""
    level: CertificationLevel
    name: str
    description: str
    prerequisites: List[str]
    requirements: List[str]
    assessment_method: str
    validity_period: int  # 月


@dataclass
class UserProfile:
    """用户档案"""
    user_id: str
    name: str
    email: str
    organization: str
    certifications: List[Dict[str, Any]]
    achievements: List[str]
    created_at: datetime.datetime
    updated_at: datetime.datetime


@dataclass
class CertificationRecord:
    """认证记录"""
    certification_id: str
    user_id: str
    level: CertificationLevel
    status: str  # pending, passed, failed, expired
    score: float
    max_score: float
    passed_at: Optional[datetime.datetime]
    expires_at: Optional[datetime.datetime]
    evidence: List[str]


class CertificationSystem:
    """认证系统"""
    
    def __init__(self, config_path: str = "certification-config.json"):
        self.config = self.load_config(config_path)
        self.requirements = self.load_requirements()
        self.users: Dict[str, UserProfile] = {}
        self.certifications: Dict[str, CertificationRecord] = {}
    
    def load_config(self, config_path: str) -> Dict[str, Any]:
        """加载配置文件"""
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        except FileNotFoundError:
            return self.get_default_config()
    
    def get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            "system": {
                "name": "正式验证框架认证体系",
                "version": "1.0.0",
                "admin_email": "admin@formal-framework.org"
            },
            "levels": {
                "foundation": {
                    "name": "基础认证",
                    "color": "#4CAF50",
                    "icon": "🌱"
                },
                "intermediate": {
                    "name": "进阶认证",
                    "color": "#2196F3",
                    "icon": "🚀"
                },
                "expert": {
                    "name": "专家认证",
                    "color": "#FF9800",
                    "icon": "⭐"
                },
                "master": {
                    "name": "大师认证",
                    "color": "#9C27B0",
                    "icon": "👑"
                }
            }
        }
    
    def load_requirements(self) -> List[CertificationRequirement]:
        """加载认证要求"""
        return [
            CertificationRequirement(
                level=CertificationLevel.FOUNDATION,
                name="正式验证基础认证",
                description="掌握正式验证的基本概念和工具使用",
                prerequisites=[],
                requirements=[
                    "完成基础理论课程学习",
                    "通过在线理论考试（80分以上）",
                    "完成3个基础实践案例",
                    "提交学习总结报告"
                ],
                assessment_method="在线考试 + 实践评估",
                validity_period=24
            ),
            CertificationRequirement(
                level=CertificationLevel.INTERMEDIATE,
                name="正式验证进阶认证",
                description="深入理解形式化方法，能够独立完成复杂验证任务",
                prerequisites=["foundation"],
                requirements=[
                    "完成进阶理论课程学习",
                    "通过在线理论考试（85分以上）",
                    "完成5个进阶实践案例",
                    "参与社区贡献（至少3次）",
                    "提交技术论文或案例研究"
                ],
                assessment_method="综合评估 + 同行评议",
                validity_period=36
            ),
            CertificationRequirement(
                level=CertificationLevel.EXPERT,
                name="正式验证专家认证",
                description="具备专家级理论水平和实践能力，能够指导他人",
                prerequisites=["intermediate"],
                requirements=[
                    "完成专家级理论课程学习",
                    "通过专家级理论考试（90分以上）",
                    "完成10个复杂实践案例",
                    "发表学术论文或技术文章",
                    "指导至少2名基础认证学员",
                    "参与标准制定或工具开发"
                ],
                assessment_method="专家评审 + 同行评议",
                validity_period=48
            ),
            CertificationRequirement(
                level=CertificationLevel.MASTER,
                name="正式验证大师认证",
                description="在正式验证领域具有卓越贡献和影响力",
                prerequisites=["expert"],
                requirements=[
                    "在正式验证领域有重大理论贡献",
                    "发表高质量学术论文（至少3篇）",
                    "开发或改进重要验证工具",
                    "在国际会议发表主题演讲",
                    "培养至少5名专家级人才",
                    "对行业发展有重要影响"
                ],
                assessment_method="大师委员会评审",
                validity_period=60
            )
        ]
    
    def register_user(self, user_id: str, name: str, email: str, organization: str = "") -> UserProfile:
        """注册用户"""
        if user_id in self.users:
            raise ValueError(f"用户 {user_id} 已存在")
        
        user = UserProfile(
            user_id=user_id,
            name=name,
            email=email,
            organization=organization,
            certifications=[],
            achievements=[],
            created_at=datetime.datetime.now(),
            updated_at=datetime.datetime.now()
        )
        
        self.users[user_id] = user
        return user
    
    def get_user(self, user_id: str) -> Optional[UserProfile]:
        """获取用户信息"""
        return self.users.get(user_id)
    
    def check_prerequisites(self, user_id: str, level: CertificationLevel) -> tuple[bool, List[str]]:
        """检查前置条件"""
        user = self.get_user(user_id)
        if not user:
            return False, ["用户不存在"]
        
        requirement = next((r for r in self.requirements if r.level == level), None)
        if not requirement:
            return False, ["认证等级不存在"]
        
        missing = []
        for prereq in requirement.prerequisites:
            has_cert = any(
                cert.get('level') == prereq and 
                cert.get('status') == 'passed' and
                self.is_certification_valid(cert)
                for cert in user.certifications
            )
            if not has_cert:
                missing.append(f"缺少 {prereq} 认证")
        
        return len(missing) == 0, missing
    
    def is_certification_valid(self, cert: Dict[str, Any]) -> bool:
        """检查认证是否有效"""
        if cert.get('status') != 'passed':
            return False
        
        expires_at = cert.get('expires_at')
        if not expires_at:
            return True
        
        try:
            expire_date = datetime.datetime.fromisoformat(expires_at)
            return datetime.datetime.now() < expire_date
        except:
            return False
    
    def start_certification(self, user_id: str, level: CertificationLevel) -> str:
        """开始认证流程"""
        can_start, missing = self.check_prerequisites(user_id, level)
        if not can_start:
            raise ValueError(f"不满足前置条件: {', '.join(missing)}")
        
        certification_id = self.generate_certification_id(user_id, level)
        
        record = CertificationRecord(
            certification_id=certification_id,
            user_id=user_id,
            level=level,
            status="pending",
            score=0.0,
            max_score=100.0,
            passed_at=None,
            expires_at=None,
            evidence=[]
        )
        
        self.certifications[certification_id] = record
        return certification_id
    
    def submit_evidence(self, certification_id: str, evidence: List[str]) -> bool:
        """提交认证证据"""
        if certification_id not in self.certifications:
            return False
        
        record = self.certifications[certification_id]
        if record.status != "pending":
            return False
        
        record.evidence.extend(evidence)
        return True
    
    def assess_certification(self, certification_id: str, score: float, assessor: str) -> bool:
        """评估认证"""
        if certification_id not in self.certifications:
            return False
        
        record = self.certifications[certification_id]
        if record.status != "pending":
            return False
        
        requirement = next((r for r in self.requirements if r.level == record.level), None)
        if not requirement:
            return False
        
        # 根据等级设置通过分数
        pass_scores = {
            CertificationLevel.FOUNDATION: 80.0,
            CertificationLevel.INTERMEDIATE: 85.0,
            CertificationLevel.EXPERT: 90.0,
            CertificationLevel.MASTER: 95.0
        }
        
        pass_score = pass_scores.get(record.level, 80.0)
        record.score = score
        record.max_score = 100.0
        
        if score >= pass_score:
            record.status = "passed"
            record.passed_at = datetime.datetime.now()
            
            # 设置过期时间
            validity_months = requirement.validity_period
            record.expires_at = record.passed_at + datetime.timedelta(days=validity_months * 30)
            
            # 更新用户档案
            user = self.get_user(record.user_id)
            if user:
                user.certifications.append({
                    'certification_id': certification_id,
                    'level': record.level.value,
                    'status': record.status,
                    'score': score,
                    'passed_at': record.passed_at.isoformat(),
                    'expires_at': record.expires_at.isoformat() if record.expires_at else None
                })
                user.updated_at = datetime.datetime.now()
        else:
            record.status = "failed"
        
        return True
    
    def generate_certification_id(self, user_id: str, level: CertificationLevel) -> str:
        """生成认证ID"""
        timestamp = datetime.datetime.now().isoformat()
        data = f"{user_id}_{level.value}_{timestamp}"
        return hashlib.md5(data.encode()).hexdigest()[:16]
    
    def get_user_certifications(self, user_id: str) -> List[Dict[str, Any]]:
        """获取用户认证记录"""
        user = self.get_user(user_id)
        if not user:
            return []
        
        return [cert for cert in user.certifications if self.is_certification_valid(cert)]
    
    def get_certification_statistics(self) -> Dict[str, Any]:
        """获取认证统计信息"""
        stats = {
            "total_users": len(self.users),
            "total_certifications": len(self.certifications),
            "by_level": {},
            "by_status": {},
            "recent_certifications": []
        }
        
        # 按等级统计
        for level in CertificationLevel:
            level_certs = [c for c in self.certifications.values() if c.level == level]
            stats["by_level"][level.value] = {
                "total": len(level_certs),
                "passed": len([c for c in level_certs if c.status == "passed"]),
                "pending": len([c for c in level_certs if c.status == "pending"]),
                "failed": len([c for c in level_certs if c.status == "failed"])
            }
        
        # 按状态统计
        for status in ["passed", "pending", "failed", "expired"]:
            count = len([c for c in self.certifications.values() if c.status == status])
            stats["by_status"][status] = count
        
        # 最近认证
        recent = sorted(
            [c for c in self.certifications.values() if c.passed_at],
            key=lambda x: x.passed_at,
            reverse=True
        )[:10]
        
        stats["recent_certifications"] = [
            {
                "user_id": cert.user_id,
                "level": cert.level.value,
                "score": cert.score,
                "passed_at": cert.passed_at.isoformat()
            }
            for cert in recent
        ]
        
        return stats
    
    def export_certificate(self, certification_id: str) -> Dict[str, Any]:
        """导出证书信息"""
        if certification_id not in self.certifications:
            return {}
        
        record = self.certifications[certification_id]
        user = self.get_user(record.user_id)
        requirement = next((r for r in self.requirements if r.level == record.level), None)
        
        if not user or not requirement or record.status != "passed":
            return {}
        
        return {
            "certificate_id": certification_id,
            "user_name": user.name,
            "user_email": user.email,
            "organization": user.organization,
            "certification_name": requirement.name,
            "level": record.level.value,
            "score": record.score,
            "passed_at": record.passed_at.isoformat(),
            "expires_at": record.expires_at.isoformat() if record.expires_at else None,
            "issued_by": self.config["system"]["name"],
            "verification_url": f"https://certificates.formal-framework.org/verify/{certification_id}"
        }
    
    def save_data(self, filepath: str = "certification-data.json"):
        """保存数据"""
        data = {
            "users": {uid: asdict(user) for uid, user in self.users.items()},
            "certifications": {cid: asdict(cert) for cid, cert in self.certifications.items()},
            "timestamp": datetime.datetime.now().isoformat()
        }
        
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False, default=str)
    
    def load_data(self, filepath: str = "certification-data.json"):
        """加载数据"""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            # 加载用户数据
            for uid, user_data in data.get("users", {}).items():
                user_data["created_at"] = datetime.datetime.fromisoformat(user_data["created_at"])
                user_data["updated_at"] = datetime.datetime.fromisoformat(user_data["updated_at"])
                self.users[uid] = UserProfile(**user_data)
            
            # 加载认证数据
            for cid, cert_data in data.get("certifications", {}).items():
                if cert_data.get("passed_at"):
                    cert_data["passed_at"] = datetime.datetime.fromisoformat(cert_data["passed_at"])
                if cert_data.get("expires_at"):
                    cert_data["expires_at"] = datetime.datetime.fromisoformat(cert_data["expires_at"])
                cert_data["level"] = CertificationLevel(cert_data["level"])
                self.certifications[cid] = CertificationRecord(**cert_data)
                
        except FileNotFoundError:
            pass  # 文件不存在时忽略


def main():
    """主函数 - 演示认证系统"""
    system = CertificationSystem()
    
    # 注册用户
    user1 = system.register_user("user001", "张三", "zhangsan@example.com", "ABC公司")
    user2 = system.register_user("user002", "李四", "lisi@example.com", "XYZ公司")
    
    print("=== 正式验证框架认证体系演示 ===")
    print(f"注册用户: {user1.name} ({user1.email})")
    print(f"注册用户: {user2.name} ({user2.email})")
    
    # 开始基础认证
    cert_id = system.start_certification("user001", CertificationLevel.FOUNDATION)
    print(f"\n用户 {user1.name} 开始基础认证，认证ID: {cert_id}")
    
    # 提交证据
    evidence = [
        "完成基础理论课程学习",
        "通过在线理论考试（85分）",
        "完成3个基础实践案例",
        "提交学习总结报告"
    ]
    system.submit_evidence(cert_id, evidence)
    print(f"提交认证证据: {len(evidence)} 项")
    
    # 评估认证
    system.assess_certification(cert_id, 85.0, "assessor001")
    print(f"认证评估完成，分数: 85.0")
    
    # 查看用户认证
    user_certs = system.get_user_certifications("user001")
    print(f"\n用户 {user1.name} 的认证记录:")
    for cert in user_certs:
        print(f"  - {cert['level']}: {cert['status']} (分数: {cert['score']})")
    
    # 获取统计信息
    stats = system.get_certification_statistics()
    print(f"\n认证统计:")
    print(f"  总用户数: {stats['total_users']}")
    print(f"  总认证数: {stats['total_certifications']}")
    print(f"  通过认证: {stats['by_status']['passed']}")
    
    # 导出证书
    certificate = system.export_certificate(cert_id)
    if certificate:
        print(f"\n证书信息:")
        print(f"  证书ID: {certificate['certificate_id']}")
        print(f"  认证名称: {certificate['certification_name']}")
        print(f"  通过时间: {certificate['passed_at']}")
    
    # 保存数据
    system.save_data()
    print(f"\n数据已保存到 certification-data.json")


if __name__ == "__main__":
    main()
