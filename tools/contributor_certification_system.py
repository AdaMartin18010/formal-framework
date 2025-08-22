#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework 贡献者认证系统

该模块实现了Formal Framework项目的贡献者认证体系，包括等级评估、技能测试、推荐机制等功能。
"""

import logging
import json
import datetime
from dataclasses import dataclass, asdict
from typing import Dict, List, Optional, Any
from enum import Enum
import sqlite3
from pathlib import Path

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class ContributorLevel(Enum):
    """贡献者等级枚举"""
    BEGINNER = "beginner"
    REGULAR = "regular"
    EXPERT = "expert"
    MAINTAINER = "maintainer"

class CertificationStatus(Enum):
    """认证状态枚举"""
    PENDING = "pending"
    APPROVED = "approved"
    REJECTED = "rejected"
    EXPIRED = "expired"

@dataclass
class Contribution:
    """贡献记录"""
    id: str
    contributor_id: str
    type: str  # issue, pr, documentation, code, review
    title: str
    description: str
    quality_score: float
    created_at: datetime.datetime
    merged_at: Optional[datetime.datetime] = None
    review_count: int = 0
    approval_count: int = 0

@dataclass
class SkillAssessment:
    """技能评估"""
    contributor_id: str
    skill_area: str
    score: float
    assessment_date: datetime.datetime
    assessor_id: str
    comments: str = ""

@dataclass
class Recommendation:
    """推荐记录"""
    id: str
    contributor_id: str
    recommender_id: str
    level: str
    reason: str
    created_at: datetime.datetime
    status: str = "pending"

@dataclass
class CertificationResult:
    """认证结果"""
    contributor_id: str
    level: str
    score: float
    valid_until: Optional[datetime.datetime]
    status: CertificationStatus
    requirements_met: List[str]
    requirements_missing: List[str]
    recommendations: List[str]

class Level1Beginner:
    """初学者等级评估器"""
    
    def __init__(self):
        self.requirements = {
            "guide_completion": "完成基础贡献指南学习",
            "issue_submission": "提交至少1个有效Issue",
            "basic_skill_test": "通过基础技能测试"
        }
    
    def evaluate(self, contributions: List[Contribution], 
                 skills: List[SkillAssessment], 
                 recommendations: List[Recommendation]) -> bool:
        """评估是否满足初学者要求"""
        # 检查指南完成情况
        guide_completed = self.check_guide_completion(contributions)
        
        # 检查Issue提交情况
        issues_submitted = len([c for c in contributions if c.type == "issue"]) >= 1
        
        # 检查基础技能测试
        basic_skills_passed = self.check_basic_skills(skills)
        
        return guide_completed and issues_submitted and basic_skills_passed
    
    def calculate_score(self, contributions: List[Contribution], 
                       skills: List[SkillAssessment], 
                       recommendations: List[Recommendation]) -> float:
        """计算初学者分数"""
        score = 0.0
        
        # 基础分数
        score += 30.0
        
        # 贡献质量分数
        if contributions:
            avg_quality = sum(c.quality_score for c in contributions) / len(contributions)
            score += avg_quality * 20.0
        
        # 技能分数
        if skills:
            avg_skill = sum(s.score for s in skills) / len(skills)
            score += avg_skill * 30.0
        
        # 推荐分数
        score += len(recommendations) * 10.0
        
        return min(score, 100.0)
    
    def get_validity_period(self) -> datetime.datetime:
        """获取有效期"""
        return datetime.datetime.now() + datetime.timedelta(days=365)
    
    def check_guide_completion(self, contributions: List[Contribution]) -> bool:
        """检查指南完成情况"""
        # 这里应该检查是否完成了贡献指南学习
        # 简化实现：检查是否有相关贡献
        return len(contributions) > 0
    
    def check_basic_skills(self, skills: List[SkillAssessment]) -> bool:
        """检查基础技能"""
        # 检查是否有基础技能评估且分数达到60分以上
        basic_skills = [s for s in skills if s.skill_area in ["git", "markdown", "basic_programming"]]
        return any(s.score >= 60.0 for s in basic_skills)

class Level2Regular:
    """常规贡献者等级评估器"""
    
    def __init__(self):
        self.requirements = {
            "valid_contributions": "完成至少5个有效贡献",
            "code_review_test": "通过代码审查测试",
            "maintainer_recommendations": "获得2个维护者推荐"
        }
    
    def evaluate(self, contributions: List[Contribution], 
                 skills: List[SkillAssessment], 
                 recommendations: List[Recommendation]) -> bool:
        """评估是否满足常规贡献者要求"""
        # 检查有效贡献数量
        valid_contributions = len([c for c in contributions if c.quality_score >= 70.0]) >= 5
        
        # 检查代码审查测试
        review_test_passed = self.check_review_test(skills)
        
        # 检查维护者推荐
        maintainer_recommendations = len([r for r in recommendations 
                                        if r.recommender_id.startswith("maintainer_")]) >= 2
        
        return valid_contributions and review_test_passed and maintainer_recommendations
    
    def calculate_score(self, contributions: List[Contribution], 
                       skills: List[SkillAssessment], 
                       recommendations: List[Recommendation]) -> float:
        """计算常规贡献者分数"""
        score = 0.0
        
        # 基础分数
        score += 50.0
        
        # 贡献质量分数
        if contributions:
            high_quality_contributions = [c for c in contributions if c.quality_score >= 70.0]
            if high_quality_contributions:
                avg_quality = sum(c.quality_score for c in high_quality_contributions) / len(high_quality_contributions)
                score += avg_quality * 0.3
        
        # 技能分数
        if skills:
            avg_skill = sum(s.score for s in skills) / len(skills)
            score += avg_skill * 0.2
        
        return min(score, 100.0)
    
    def get_validity_period(self) -> datetime.datetime:
        """获取有效期"""
        return datetime.datetime.now() + datetime.timedelta(days=730)
    
    def check_review_test(self, skills: List[SkillAssessment]) -> bool:
        """检查代码审查测试"""
        review_skills = [s for s in skills if s.skill_area == "code_review"]
        return any(s.score >= 70.0 for s in review_skills)

class Level3Expert:
    """专家贡献者等级评估器"""
    
    def __init__(self):
        self.requirements = {
            "high_quality_contributions": "完成至少20个高质量贡献",
            "expert_review": "通过专家评审",
            "domain_expertise": "在特定领域有专长"
        }
    
    def evaluate(self, contributions: List[Contribution], 
                 skills: List[SkillAssessment], 
                 recommendations: List[Recommendation]) -> bool:
        """评估是否满足专家要求"""
        # 检查高质量贡献数量
        high_quality_contributions = len([c for c in contributions if c.quality_score >= 85.0]) >= 20
        
        # 检查专家评审
        expert_review_passed = self.check_expert_review(recommendations)
        
        # 检查领域专长
        domain_expertise = self.check_domain_expertise(skills)
        
        return high_quality_contributions and expert_review_passed and domain_expertise
    
    def calculate_score(self, contributions: List[Contribution], 
                       skills: List[SkillAssessment], 
                       recommendations: List[Recommendation]) -> float:
        """计算专家分数"""
        score = 0.0
        
        # 基础分数
        score += 70.0
        
        # 高质量贡献分数
        high_quality_contributions = [c for c in contributions if c.quality_score >= 85.0]
        if high_quality_contributions:
            avg_quality = sum(c.quality_score for c in high_quality_contributions) / len(high_quality_contributions)
            score += avg_quality * 0.2
        
        # 专家推荐分数
        expert_recommendations = [r for r in recommendations if r.recommender_id.startswith("expert_")]
        score += len(expert_recommendations) * 5.0
        
        return min(score, 100.0)
    
    def get_validity_period(self) -> datetime.datetime:
        """获取有效期"""
        return datetime.datetime.now() + datetime.timedelta(days=1095)
    
    def check_expert_review(self, recommendations: List[Recommendation]) -> bool:
        """检查专家评审"""
        expert_recommendations = [r for r in recommendations if r.recommender_id.startswith("expert_")]
        return len(expert_recommendations) >= 3
    
    def check_domain_expertise(self, skills: List[SkillAssessment]) -> bool:
        """检查领域专长"""
        # 检查是否有某个领域的技能分数达到90分以上
        return any(s.score >= 90.0 for s in skills)

class Level4Maintainer:
    """维护者等级评估器"""
    
    def __init__(self):
        self.requirements = {
            "long_term_contribution": "长期稳定贡献",
            "maintainer_committee_review": "通过维护者委员会评审",
            "project_management_ability": "具备项目管理能力"
        }
    
    def evaluate(self, contributions: List[Contribution], 
                 skills: List[SkillAssessment], 
                 recommendations: List[Recommendation]) -> bool:
        """评估是否满足维护者要求"""
        # 检查长期贡献
        long_term_contribution = self.check_long_term_contribution(contributions)
        
        # 检查委员会评审
        committee_review_passed = self.check_committee_review(recommendations)
        
        # 检查项目管理能力
        project_management_ability = self.check_project_management(skills)
        
        return long_term_contribution and committee_review_passed and project_management_ability
    
    def calculate_score(self, contributions: List[Contribution], 
                       skills: List[SkillAssessment], 
                       recommendations: List[Recommendation]) -> float:
        """计算维护者分数"""
        score = 0.0
        
        # 基础分数
        score += 85.0
        
        # 长期贡献分数
        if contributions:
            recent_contributions = [c for c in contributions 
                                  if c.created_at > datetime.datetime.now() - datetime.timedelta(days=365)]
            if recent_contributions:
                avg_quality = sum(c.quality_score for c in recent_contributions) / len(recent_contributions)
                score += avg_quality * 0.1
        
        # 委员会推荐分数
        committee_recommendations = [r for r in recommendations 
                                   if r.recommender_id.startswith("committee_")]
        score += len(committee_recommendations) * 3.0
        
        return min(score, 100.0)
    
    def get_validity_period(self) -> datetime.datetime:
        """获取有效期"""
        return datetime.datetime.now() + datetime.timedelta(days=1825)
    
    def check_long_term_contribution(self, contributions: List[Contribution]) -> bool:
        """检查长期贡献"""
        # 检查是否有超过1年的持续贡献
        if not contributions:
            return False
        
        earliest_contribution = min(c.created_at for c in contributions)
        return datetime.datetime.now() - earliest_contribution > datetime.timedelta(days=365)
    
    def check_committee_review(self, recommendations: List[Recommendation]) -> bool:
        """检查委员会评审"""
        committee_recommendations = [r for r in recommendations 
                                   if r.recommender_id.startswith("committee_")]
        return len(committee_recommendations) >= 5
    
    def check_project_management(self, skills: List[SkillAssessment]) -> bool:
        """检查项目管理能力"""
        management_skills = [s for s in skills if s.skill_area in ["project_management", "team_leadership"]]
        return any(s.score >= 85.0 for s in management_skills)

class CertificationDatabase:
    """认证数据库"""
    
    def __init__(self, db_path: str = "certification.db"):
        self.db_path = db_path
        self.init_database()
    
    def init_database(self):
        """初始化数据库"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS contributors (
                    id TEXT PRIMARY KEY,
                    name TEXT NOT NULL,
                    email TEXT,
                    github_username TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS contributions (
                    id TEXT PRIMARY KEY,
                    contributor_id TEXT,
                    type TEXT,
                    title TEXT,
                    description TEXT,
                    quality_score REAL,
                    created_at TIMESTAMP,
                    merged_at TIMESTAMP,
                    review_count INTEGER DEFAULT 0,
                    approval_count INTEGER DEFAULT 0,
                    FOREIGN KEY (contributor_id) REFERENCES contributors (id)
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS skill_assessments (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    contributor_id TEXT,
                    skill_area TEXT,
                    score REAL,
                    assessment_date TIMESTAMP,
                    assessor_id TEXT,
                    comments TEXT,
                    FOREIGN KEY (contributor_id) REFERENCES contributors (id)
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS recommendations (
                    id TEXT PRIMARY KEY,
                    contributor_id TEXT,
                    recommender_id TEXT,
                    level TEXT,
                    reason TEXT,
                    created_at TIMESTAMP,
                    status TEXT DEFAULT 'pending',
                    FOREIGN KEY (contributor_id) REFERENCES contributors (id)
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS certifications (
                    id TEXT PRIMARY KEY,
                    contributor_id TEXT,
                    level TEXT,
                    score REAL,
                    valid_until TIMESTAMP,
                    status TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    FOREIGN KEY (contributor_id) REFERENCES contributors (id)
                )
            """)
    
    def get_contributor(self, contributor_id: str) -> Optional[Dict]:
        """获取贡献者信息"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute(
                "SELECT * FROM contributors WHERE id = ?", 
                (contributor_id,)
            )
            row = cursor.fetchone()
            if row:
                return dict(zip([col[0] for col in cursor.description], row))
            return None
    
    def add_contributor(self, contributor_id: str, name: str, 
                       email: str = None, github_username: str = None):
        """添加贡献者"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute(
                "INSERT OR REPLACE INTO contributors (id, name, email, github_username) VALUES (?, ?, ?, ?)",
                (contributor_id, name, email, github_username)
            )
    
    def add_contribution(self, contribution: Contribution):
        """添加贡献记录"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO contributions 
                (id, contributor_id, type, title, description, quality_score, 
                 created_at, merged_at, review_count, approval_count)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                contribution.id, contribution.contributor_id, contribution.type,
                contribution.title, contribution.description, contribution.quality_score,
                contribution.created_at, contribution.merged_at,
                contribution.review_count, contribution.approval_count
            ))
    
    def get_contributions(self, contributor_id: str) -> List[Contribution]:
        """获取贡献者的所有贡献"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute(
                "SELECT * FROM contributions WHERE contributor_id = ? ORDER BY created_at DESC",
                (contributor_id,)
            )
            contributions = []
            for row in cursor.fetchall():
                contribution = Contribution(
                    id=row[0], contributor_id=row[1], type=row[2],
                    title=row[3], description=row[4], quality_score=row[5],
                    created_at=datetime.datetime.fromisoformat(row[6]),
                    merged_at=datetime.datetime.fromisoformat(row[7]) if row[7] else None,
                    review_count=row[8], approval_count=row[9]
                )
                contributions.append(contribution)
            return contributions
    
    def add_skill_assessment(self, assessment: SkillAssessment):
        """添加技能评估"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT INTO skill_assessments 
                (contributor_id, skill_area, score, assessment_date, assessor_id, comments)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (
                assessment.contributor_id, assessment.skill_area, assessment.score,
                assessment.assessment_date, assessment.assessor_id, assessment.comments
            ))
    
    def get_skill_assessments(self, contributor_id: str) -> List[SkillAssessment]:
        """获取贡献者的技能评估"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute(
                "SELECT * FROM skill_assessments WHERE contributor_id = ? ORDER BY assessment_date DESC",
                (contributor_id,)
            )
            assessments = []
            for row in cursor.fetchall():
                assessment = SkillAssessment(
                    contributor_id=row[1], skill_area=row[2], score=row[3],
                    assessment_date=datetime.datetime.fromisoformat(row[4]),
                    assessor_id=row[5], comments=row[6]
                )
                assessments.append(assessment)
            return assessments
    
    def add_recommendation(self, recommendation: Recommendation):
        """添加推荐记录"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO recommendations 
                (id, contributor_id, recommender_id, level, reason, created_at, status)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (
                recommendation.id, recommendation.contributor_id,
                recommendation.recommender_id, recommendation.level,
                recommendation.reason, recommendation.created_at, recommendation.status
            ))
    
    def get_recommendations(self, contributor_id: str) -> List[Recommendation]:
        """获取贡献者的推荐记录"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute(
                "SELECT * FROM recommendations WHERE contributor_id = ? ORDER BY created_at DESC",
                (contributor_id,)
            )
            recommendations = []
            for row in cursor.fetchall():
                recommendation = Recommendation(
                    id=row[0], contributor_id=row[1], recommender_id=row[2],
                    level=row[3], reason=row[4],
                    created_at=datetime.datetime.fromisoformat(row[5]),
                    status=row[6]
                )
                recommendations.append(recommendation)
            return recommendations
    
    def save_certification(self, certification: CertificationResult):
        """保存认证结果"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO certifications 
                (id, contributor_id, level, score, valid_until, status)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (
                f"cert_{certification.contributor_id}_{datetime.datetime.now().strftime('%Y%m%d')}",
                certification.contributor_id, certification.level, certification.score,
                certification.valid_until, certification.status.value
            ))

class ContributorCertificationSystem:
    """贡献者认证系统主类"""
    
    def __init__(self, db_path: str = "certification.db"):
        self.levels = {
            ContributorLevel.BEGINNER.value: Level1Beginner(),
            ContributorLevel.REGULAR.value: Level2Regular(),
            ContributorLevel.EXPERT.value: Level3Expert(),
            ContributorLevel.MAINTAINER.value: Level4Maintainer()
        }
        self.certification_database = CertificationDatabase(db_path)
        
        logger.info("贡献者认证系统初始化完成")
    
    def evaluate_contributor(self, contributor_id: str) -> CertificationResult:
        """评估贡献者等级"""
        logger.info(f"开始评估贡献者: {contributor_id}")
        
        # 获取贡献者信息
        contributor = self.certification_database.get_contributor(contributor_id)
        if not contributor:
            logger.warning(f"贡献者不存在: {contributor_id}")
            return CertificationResult(
                contributor_id=contributor_id,
                level="none",
                score=0,
                valid_until=None,
                status=CertificationStatus.REJECTED,
                requirements_met=[],
                requirements_missing=["贡献者信息不存在"],
                recommendations=["请先注册为贡献者"]
            )
        
        # 收集贡献数据
        contributions = self.certification_database.get_contributions(contributor_id)
        skills = self.certification_database.get_skill_assessments(contributor_id)
        recommendations = self.certification_database.get_recommendations(contributor_id)
        
        logger.info(f"收集到 {len(contributions)} 个贡献, {len(skills)} 个技能评估, {len(recommendations)} 个推荐")
        
        # 评估等级
        for level_name, level in self.levels.items():
            if level.evaluate(contributions, skills, recommendations):
                score = level.calculate_score(contributions, skills, recommendations)
                valid_until = level.get_validity_period()
                
                # 确定状态
                status = CertificationStatus.APPROVED if score >= 70.0 else CertificationStatus.PENDING
                
                # 生成要求满足情况
                requirements_met = self.get_requirements_met(level_name, contributions, skills, recommendations)
                requirements_missing = self.get_requirements_missing(level_name, contributions, skills, recommendations)
                
                result = CertificationResult(
                    contributor_id=contributor_id,
                    level=level_name,
                    score=score,
                    valid_until=valid_until,
                    status=status,
                    requirements_met=requirements_met,
                    requirements_missing=requirements_missing,
                    recommendations=self.generate_recommendations(level_name, requirements_missing)
                )
                
                # 保存认证结果
                self.certification_database.save_certification(result)
                
                logger.info(f"贡献者 {contributor_id} 评估完成: {level_name}, 分数: {score}")
                return result
        
        # 如果没有达到任何等级
        return CertificationResult(
            contributor_id=contributor_id,
            level="none",
            score=0,
            valid_until=None,
            status=CertificationStatus.REJECTED,
            requirements_met=[],
            requirements_missing=["未达到任何等级要求"],
            recommendations=["请继续参与项目贡献，提升技能水平"]
        )
    
    def get_requirements_met(self, level: str, contributions: List[Contribution], 
                           skills: List[SkillAssessment], 
                           recommendations: List[Recommendation]) -> List[str]:
        """获取已满足的要求"""
        if level == ContributorLevel.BEGINNER.value:
            met = []
            if len(contributions) > 0:
                met.append("完成基础贡献指南学习")
            if len([c for c in contributions if c.type == "issue"]) >= 1:
                met.append("提交至少1个有效Issue")
            if any(s.score >= 60.0 for s in skills):
                met.append("通过基础技能测试")
            return met
        # 其他等级的实现类似...
        return []
    
    def get_requirements_missing(self, level: str, contributions: List[Contribution], 
                               skills: List[SkillAssessment], 
                               recommendations: List[Recommendation]) -> List[str]:
        """获取未满足的要求"""
        if level == ContributorLevel.BEGINNER.value:
            missing = []
            if len(contributions) == 0:
                missing.append("完成基础贡献指南学习")
            if len([c for c in contributions if c.type == "issue"]) < 1:
                missing.append("提交至少1个有效Issue")
            if not any(s.score >= 60.0 for s in skills):
                missing.append("通过基础技能测试")
            return missing
        # 其他等级的实现类似...
        return []
    
    def generate_recommendations(self, level: str, missing_requirements: List[str]) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        if "完成基础贡献指南学习" in missing_requirements:
            recommendations.append("请阅读项目的贡献指南文档")
        
        if "提交至少1个有效Issue" in missing_requirements:
            recommendations.append("请提交一个Issue来报告问题或建议改进")
        
        if "通过基础技能测试" in missing_requirements:
            recommendations.append("请参加基础技能测试，提升Git、Markdown等基础技能")
        
        return recommendations
    
    def add_sample_data(self):
        """添加示例数据用于测试"""
        # 添加示例贡献者
        self.certification_database.add_contributor(
            "contributor_001", "张三", "zhangsan@example.com", "zhangsan"
        )
        
        # 添加示例贡献
        contribution = Contribution(
            id="cont_001",
            contributor_id="contributor_001",
            type="issue",
            title="文档改进建议",
            description="建议改进README文档的结构",
            quality_score=85.0,
            created_at=datetime.datetime.now() - datetime.timedelta(days=30),
            merged_at=datetime.datetime.now() - datetime.timedelta(days=25)
        )
        self.certification_database.add_contribution(contribution)
        
        # 添加示例技能评估
        skill_assessment = SkillAssessment(
            contributor_id="contributor_001",
            skill_area="git",
            score=75.0,
            assessment_date=datetime.datetime.now() - datetime.timedelta(days=20),
            assessor_id="maintainer_001",
            comments="Git基础操作熟练"
        )
        self.certification_database.add_skill_assessment(skill_assessment)
        
        logger.info("示例数据添加完成")

def main():
    """主函数"""
    # 创建认证系统
    certification_system = ContributorCertificationSystem()
    
    # 添加示例数据
    certification_system.add_sample_data()
    
    # 评估贡献者
    result = certification_system.evaluate_contributor("contributor_001")
    
    # 输出结果
    print("认证评估结果:")
    print(f"贡献者ID: {result.contributor_id}")
    print(f"等级: {result.level}")
    print(f"分数: {result.score}")
    print(f"状态: {result.status.value}")
    print(f"有效期至: {result.valid_until}")
    print(f"已满足要求: {result.requirements_met}")
    print(f"未满足要求: {result.requirements_missing}")
    print(f"改进建议: {result.recommendations}")

if __name__ == "__main__":
    main()
