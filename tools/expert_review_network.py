#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework 专家评审网络系统

该模块实现了Formal Framework项目的专家评审网络，包括专家管理、评审任务分配、评审流程管理等功能。
"""

import logging
import json
import datetime
from dataclasses import dataclass, asdict
from typing import Dict, List, Optional, Any, Set
from enum import Enum
import sqlite3
from pathlib import Path
import random

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class ReviewStatus(Enum):
    """评审状态枚举"""
    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    REJECTED = "rejected"
    EXPIRED = "expired"

class ReviewPriority(Enum):
    """评审优先级枚举"""
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    URGENT = "urgent"

class ExpertCategory(Enum):
    """专家分类枚举"""
    ACADEMIC = "academic"
    INDUSTRY = "industry"
    DOMAIN = "domain"
    METHODOLOGY = "methodology"

@dataclass
class Expert:
    """专家信息"""
    id: str
    name: str
    email: str
    organization: str
    title: str
    categories: List[str]  # 专家分类
    expertise_areas: List[str]  # 专业领域
    availability: bool = True
    current_workload: int = 0
    max_workload: int = 5
    rating: float = 0.0
    review_count: int = 0
    created_at: datetime.datetime = None

@dataclass
class ReviewAssignment:
    """评审任务分配"""
    id: str
    content_id: str
    expert_id: str
    review_type: str
    priority: ReviewPriority
    deadline: datetime.datetime
    status: ReviewStatus = ReviewStatus.PENDING
    assigned_at: datetime.datetime = None
    started_at: Optional[datetime.datetime] = None
    completed_at: Optional[datetime.datetime] = None

@dataclass
class ReviewResult:
    """评审结果"""
    id: str
    assignment_id: str
    expert_id: str
    content_id: str
    quality_score: float
    technical_accuracy: float
    completeness: float
    clarity: float
    comments: str
    recommendations: List[str]
    status: ReviewStatus
    submitted_at: datetime.datetime

@dataclass
class ContentItem:
    """内容项"""
    id: str
    title: str
    content_type: str  # document, code, design, research
    category: str
    author_id: str
    current_quality_score: float
    review_count: int = 0
    created_at: datetime.datetime = None
    updated_at: datetime.datetime = None

class ExpertDatabase:
    """专家数据库"""
    
    def __init__(self, db_path: str = "expert_review.db"):
        self.db_path = db_path
        self.init_database()
    
    def init_database(self):
        """初始化数据库"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS experts (
                    id TEXT PRIMARY KEY,
                    name TEXT NOT NULL,
                    email TEXT UNIQUE,
                    organization TEXT,
                    title TEXT,
                    categories TEXT,
                    expertise_areas TEXT,
                    availability BOOLEAN DEFAULT 1,
                    current_workload INTEGER DEFAULT 0,
                    max_workload INTEGER DEFAULT 5,
                    rating REAL DEFAULT 0.0,
                    review_count INTEGER DEFAULT 0,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS content_items (
                    id TEXT PRIMARY KEY,
                    title TEXT NOT NULL,
                    content_type TEXT,
                    category TEXT,
                    author_id TEXT,
                    current_quality_score REAL DEFAULT 0.0,
                    review_count INTEGER DEFAULT 0,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS review_assignments (
                    id TEXT PRIMARY KEY,
                    content_id TEXT,
                    expert_id TEXT,
                    review_type TEXT,
                    priority TEXT,
                    deadline TIMESTAMP,
                    status TEXT DEFAULT 'pending',
                    assigned_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    started_at TIMESTAMP,
                    completed_at TIMESTAMP,
                    FOREIGN KEY (content_id) REFERENCES content_items (id),
                    FOREIGN KEY (expert_id) REFERENCES experts (id)
                )
            """)
            
            conn.execute("""
                CREATE TABLE IF NOT EXISTS review_results (
                    id TEXT PRIMARY KEY,
                    assignment_id TEXT,
                    expert_id TEXT,
                    content_id TEXT,
                    quality_score REAL,
                    technical_accuracy REAL,
                    completeness REAL,
                    clarity REAL,
                    comments TEXT,
                    recommendations TEXT,
                    status TEXT,
                    submitted_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    FOREIGN KEY (assignment_id) REFERENCES review_assignments (id),
                    FOREIGN KEY (expert_id) REFERENCES experts (id),
                    FOREIGN KEY (content_id) REFERENCES content_items (id)
                )
            """)
    
    def add_expert(self, expert: Expert):
        """添加专家"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO experts 
                (id, name, email, organization, title, categories, expertise_areas,
                 availability, current_workload, max_workload, rating, review_count, created_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                expert.id, expert.name, expert.email, expert.organization, expert.title,
                json.dumps(expert.categories), json.dumps(expert.expertise_areas),
                expert.availability, expert.current_workload, expert.max_workload,
                expert.rating, expert.review_count, expert.created_at or datetime.datetime.now()
            ))
    
    def get_expert(self, expert_id: str) -> Optional[Expert]:
        """获取专家信息"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute(
                "SELECT * FROM experts WHERE id = ?", 
                (expert_id,)
            )
            row = cursor.fetchone()
            if row:
                return Expert(
                    id=row[0], name=row[1], email=row[2], organization=row[3],
                    title=row[4], categories=json.loads(row[5]), expertise_areas=json.loads(row[6]),
                    availability=bool(row[7]), current_workload=row[8], max_workload=row[9],
                    rating=row[10], review_count=row[11],
                    created_at=datetime.datetime.fromisoformat(row[12])
                )
            return None
    
    def get_available_experts(self, categories: List[str] = None, 
                            expertise_areas: List[str] = None) -> List[Expert]:
        """获取可用专家"""
        with sqlite3.connect(self.db_path) as conn:
            query = "SELECT * FROM experts WHERE availability = 1 AND current_workload < max_workload"
            params = []
            
            if categories:
                query += " AND ("
                for i, category in enumerate(categories):
                    if i > 0:
                        query += " OR "
                    query += "categories LIKE ?"
                    params.append(f"%{category}%")
                query += ")"
            
            if expertise_areas:
                query += " AND ("
                for i, area in enumerate(expertise_areas):
                    if i > 0:
                        query += " OR "
                    query += "expertise_areas LIKE ?"
                    params.append(f"%{area}%")
                query += ")"
            
            query += " ORDER BY rating DESC, current_workload ASC"
            
            cursor = conn.execute(query, params)
            experts = []
            for row in cursor.fetchall():
                expert = Expert(
                    id=row[0], name=row[1], email=row[2], organization=row[3],
                    title=row[4], categories=json.loads(row[5]), expertise_areas=json.loads(row[6]),
                    availability=bool(row[7]), current_workload=row[8], max_workload=row[9],
                    rating=row[10], review_count=row[11],
                    created_at=datetime.datetime.fromisoformat(row[12])
                )
                experts.append(expert)
            return experts
    
    def update_expert_workload(self, expert_id: str, workload_change: int):
        """更新专家工作负载"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute(
                "UPDATE experts SET current_workload = current_workload + ? WHERE id = ?",
                (workload_change, expert_id)
            )
    
    def add_content_item(self, content: ContentItem):
        """添加内容项"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO content_items 
                (id, title, content_type, category, author_id, current_quality_score,
                 review_count, created_at, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                content.id, content.title, content.content_type, content.category,
                content.author_id, content.current_quality_score, content.review_count,
                content.created_at or datetime.datetime.now(),
                content.updated_at or datetime.datetime.now()
            ))
    
    def get_content_item(self, content_id: str) -> Optional[ContentItem]:
        """获取内容项"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute(
                "SELECT * FROM content_items WHERE id = ?", 
                (content_id,)
            )
            row = cursor.fetchone()
            if row:
                return ContentItem(
                    id=row[0], title=row[1], content_type=row[2], category=row[3],
                    author_id=row[4], current_quality_score=row[5], review_count=row[6],
                    created_at=datetime.datetime.fromisoformat(row[7]),
                    updated_at=datetime.datetime.fromisoformat(row[8])
                )
            return None
    
    def add_review_assignment(self, assignment: ReviewAssignment):
        """添加评审任务"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO review_assignments 
                (id, content_id, expert_id, review_type, priority, deadline,
                 status, assigned_at, started_at, completed_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                assignment.id, assignment.content_id, assignment.expert_id,
                assignment.review_type, assignment.priority.value, assignment.deadline,
                assignment.status.value, assignment.assigned_at or datetime.datetime.now(),
                assignment.started_at, assignment.completed_at
            ))
    
    def get_review_assignments(self, expert_id: str = None, 
                             status: ReviewStatus = None) -> List[ReviewAssignment]:
        """获取评审任务"""
        with sqlite3.connect(self.db_path) as conn:
            query = "SELECT * FROM review_assignments"
            params = []
            
            if expert_id:
                query += " WHERE expert_id = ?"
                params.append(expert_id)
            
            if status:
                if expert_id:
                    query += " AND status = ?"
                else:
                    query += " WHERE status = ?"
                params.append(status.value)
            
            query += " ORDER BY deadline ASC"
            
            cursor = conn.execute(query, params)
            assignments = []
            for row in cursor.fetchall():
                assignment = ReviewAssignment(
                    id=row[0], content_id=row[1], expert_id=row[2],
                    review_type=row[3], priority=ReviewPriority(row[4]),
                    deadline=datetime.datetime.fromisoformat(row[5]),
                    status=ReviewStatus(row[6]),
                    assigned_at=datetime.datetime.fromisoformat(row[7]),
                    started_at=datetime.datetime.fromisoformat(row[8]) if row[8] else None,
                    completed_at=datetime.datetime.fromisoformat(row[9]) if row[9] else None
                )
                assignments.append(assignment)
            return assignments
    
    def update_assignment_status(self, assignment_id: str, status: ReviewStatus,
                               started_at: datetime.datetime = None,
                               completed_at: datetime.datetime = None):
        """更新任务状态"""
        with sqlite3.connect(self.db_path) as conn:
            if started_at and completed_at:
                conn.execute("""
                    UPDATE review_assignments 
                    SET status = ?, started_at = ?, completed_at = ?
                    WHERE id = ?
                """, (status.value, started_at, completed_at, assignment_id))
            elif started_at:
                conn.execute("""
                    UPDATE review_assignments 
                    SET status = ?, started_at = ?
                    WHERE id = ?
                """, (status.value, started_at, assignment_id))
            else:
                conn.execute("""
                    UPDATE review_assignments 
                    SET status = ?
                    WHERE id = ?
                """, (status.value, assignment_id))
    
    def add_review_result(self, result: ReviewResult):
        """添加评审结果"""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT OR REPLACE INTO review_results 
                (id, assignment_id, expert_id, content_id, quality_score,
                 technical_accuracy, completeness, clarity, comments,
                 recommendations, status, submitted_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                result.id, result.assignment_id, result.expert_id, result.content_id,
                result.quality_score, result.technical_accuracy, result.completeness,
                result.clarity, result.comments, json.dumps(result.recommendations),
                result.status.value, result.submitted_at
            ))
    
    def get_review_results(self, content_id: str) -> List[ReviewResult]:
        """获取评审结果"""
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.execute(
                "SELECT * FROM review_results WHERE content_id = ? ORDER BY submitted_at DESC",
                (content_id,)
            )
            results = []
            for row in cursor.fetchall():
                result = ReviewResult(
                    id=row[0], assignment_id=row[1], expert_id=row[2], content_id=row[3],
                    quality_score=row[4], technical_accuracy=row[5], completeness=row[6],
                    clarity=row[7], comments=row[8], recommendations=json.loads(row[9]),
                    status=ReviewStatus(row[10]),
                    submitted_at=datetime.datetime.fromisoformat(row[11])
                )
                results.append(result)
            return results

class ExpertReviewNetwork:
    """专家评审网络主类"""
    
    def __init__(self, db_path: str = "expert_review.db"):
        self.expert_database = ExpertDatabase(db_path)
        self.review_queue = []
        
        logger.info("专家评审网络初始化完成")
    
    def add_expert(self, expert: Expert):
        """添加专家"""
        self.expert_database.add_expert(expert)
        logger.info(f"专家 {expert.name} 已添加到评审网络")
    
    def add_content_for_review(self, content: ContentItem):
        """添加需要评审的内容"""
        self.expert_database.add_content_item(content)
        logger.info(f"内容 {content.title} 已添加到评审队列")
    
    def assign_review(self, content_id: str, review_type: str = "general",
                     priority: ReviewPriority = ReviewPriority.MEDIUM,
                     required_categories: List[str] = None,
                     required_expertise: List[str] = None,
                     deadline_days: int = 7) -> List[ReviewAssignment]:
        """分配评审任务"""
        logger.info(f"开始为内容 {content_id} 分配评审任务")
        
        # 获取内容信息
        content = self.expert_database.get_content_item(content_id)
        if not content:
            logger.error(f"内容 {content_id} 不存在")
            return []
        
        # 确定需要的专家类型
        if not required_categories:
            required_categories = self.determine_required_categories(content)
        
        if not required_expertise:
            required_expertise = self.determine_required_expertise(content)
        
        # 获取可用专家
        available_experts = self.expert_database.get_available_experts(
            categories=required_categories,
            expertise_areas=required_expertise
        )
        
        if not available_experts:
            logger.warning(f"没有找到合适的专家来评审内容 {content_id}")
            return []
        
        # 根据优先级和内容类型确定需要的专家数量
        expert_count = self.determine_expert_count(priority, content.content_type)
        
        # 选择专家
        selected_experts = self.select_experts(available_experts, expert_count, priority)
        
        # 创建评审任务
        assignments = []
        deadline = datetime.datetime.now() + datetime.timedelta(days=deadline_days)
        
        for expert in selected_experts:
            assignment = ReviewAssignment(
                id=f"review_{content_id}_{expert.id}_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}",
                content_id=content_id,
                expert_id=expert.id,
                review_type=review_type,
                priority=priority,
                deadline=deadline
            )
            
            self.expert_database.add_review_assignment(assignment)
            self.expert_database.update_expert_workload(expert.id, 1)
            assignments.append(assignment)
            
            logger.info(f"已为专家 {expert.name} 分配评审任务 {assignment.id}")
        
        return assignments
    
    def determine_required_categories(self, content: ContentItem) -> List[str]:
        """确定需要的专家分类"""
        category_mapping = {
            "document": [ExpertCategory.ACADEMIC.value, ExpertCategory.METHODOLOGY.value],
            "code": [ExpertCategory.INDUSTRY.value, ExpertCategory.METHODOLOGY.value],
            "design": [ExpertCategory.INDUSTRY.value, ExpertCategory.DOMAIN.value],
            "research": [ExpertCategory.ACADEMIC.value, ExpertCategory.DOMAIN.value]
        }
        return category_mapping.get(content.content_type, [ExpertCategory.ACADEMIC.value])
    
    def determine_required_expertise(self, content: ContentItem) -> List[str]:
        """确定需要的专业领域"""
        # 根据内容类别确定专业领域
        expertise_mapping = {
            "formal_methods": ["形式化方法", "数学逻辑", "定理证明"],
            "software_engineering": ["软件工程", "软件架构", "设计模式"],
            "ai_ml": ["人工智能", "机器学习", "深度学习"],
            "cloud_native": ["云原生", "容器化", "微服务"],
            "web3": ["区块链", "智能合约", "去中心化"]
        }
        return expertise_mapping.get(content.category, ["通用技术"])
    
    def determine_expert_count(self, priority: ReviewPriority, content_type: str) -> int:
        """确定需要的专家数量"""
        base_count = {
            ReviewPriority.LOW: 1,
            ReviewPriority.MEDIUM: 2,
            ReviewPriority.HIGH: 3,
            ReviewPriority.URGENT: 4
        }
        
        type_multiplier = {
            "document": 1,
            "code": 1.5,
            "design": 2,
            "research": 2.5
        }
        
        base = base_count.get(priority, 2)
        multiplier = type_multiplier.get(content_type, 1)
        
        return max(1, int(base * multiplier))
    
    def select_experts(self, available_experts: List[Expert], count: int, 
                      priority: ReviewPriority) -> List[Expert]:
        """选择专家"""
        # 根据优先级和专家评分进行排序
        if priority in [ReviewPriority.HIGH, ReviewPriority.URGENT]:
            # 高优先级任务优先选择高评分专家
            sorted_experts = sorted(available_experts, 
                                  key=lambda x: (x.rating, -x.current_workload), 
                                  reverse=True)
        else:
            # 普通任务平衡评分和工作负载
            sorted_experts = sorted(available_experts, 
                                  key=lambda x: (x.rating * 0.7 - x.current_workload * 0.3), 
                                  reverse=True)
        
        return sorted_experts[:count]
    
    def start_review(self, assignment_id: str, expert_id: str):
        """开始评审"""
        assignment = self.get_assignment_by_id(assignment_id)
        if not assignment:
            logger.error(f"评审任务 {assignment_id} 不存在")
            return False
        
        if assignment.expert_id != expert_id:
            logger.error(f"专家 {expert_id} 无权执行任务 {assignment_id}")
            return False
        
        if assignment.status != ReviewStatus.PENDING:
            logger.error(f"评审任务 {assignment_id} 状态不正确: {assignment.status}")
            return False
        
        # 更新任务状态
        self.expert_database.update_assignment_status(
            assignment_id, ReviewStatus.IN_PROGRESS, 
            started_at=datetime.datetime.now()
        )
        
        logger.info(f"专家 {expert_id} 开始评审任务 {assignment_id}")
        return True
    
    def submit_review(self, assignment_id: str, expert_id: str, 
                     quality_score: float, technical_accuracy: float,
                     completeness: float, clarity: float, comments: str,
                     recommendations: List[str]) -> bool:
        """提交评审结果"""
        assignment = self.get_assignment_by_id(assignment_id)
        if not assignment:
            logger.error(f"评审任务 {assignment_id} 不存在")
            return False
        
        if assignment.expert_id != expert_id:
            logger.error(f"专家 {expert_id} 无权提交任务 {assignment_id} 的结果")
            return False
        
        # 创建评审结果
        result = ReviewResult(
            id=f"result_{assignment_id}_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}",
            assignment_id=assignment_id,
            expert_id=expert_id,
            content_id=assignment.content_id,
            quality_score=quality_score,
            technical_accuracy=technical_accuracy,
            completeness=completeness,
            clarity=clarity,
            comments=comments,
            recommendations=recommendations,
            status=ReviewStatus.COMPLETED,
            submitted_at=datetime.datetime.now()
        )
        
        # 保存评审结果
        self.expert_database.add_review_result(result)
        
        # 更新任务状态
        self.expert_database.update_assignment_status(
            assignment_id, ReviewStatus.COMPLETED,
            completed_at=datetime.datetime.now()
        )
        
        # 更新专家工作负载
        self.expert_database.update_expert_workload(expert_id, -1)
        
        # 更新内容质量分数
        self.update_content_quality(assignment.content_id)
        
        logger.info(f"专家 {expert_id} 完成评审任务 {assignment_id}")
        return True
    
    def get_assignment_by_id(self, assignment_id: str) -> Optional[ReviewAssignment]:
        """根据ID获取评审任务"""
        assignments = self.expert_database.get_review_assignments()
        for assignment in assignments:
            if assignment.id == assignment_id:
                return assignment
        return None
    
    def update_content_quality(self, content_id: str):
        """更新内容质量分数"""
        results = self.expert_database.get_review_results(content_id)
        if not results:
            return
        
        # 计算平均质量分数
        avg_quality = sum(r.quality_score for r in results) / len(results)
        
        # 更新内容项的质量分数
        with sqlite3.connect(self.expert_database.db_path) as conn:
            conn.execute("""
                UPDATE content_items 
                SET current_quality_score = ?, review_count = ?, updated_at = ?
                WHERE id = ?
            """, (avg_quality, len(results), datetime.datetime.now(), content_id))
        
        logger.info(f"内容 {content_id} 质量分数已更新为 {avg_quality:.2f}")
    
    def get_expert_statistics(self, expert_id: str) -> Dict[str, Any]:
        """获取专家统计信息"""
        expert = self.expert_database.get_expert(expert_id)
        if not expert:
            return {}
        
        assignments = self.expert_database.get_review_assignments(expert_id=expert_id)
        completed_assignments = [a for a in assignments if a.status == ReviewStatus.COMPLETED]
        
        # 计算平均评审质量
        avg_quality = 0.0
        if completed_assignments:
            total_quality = 0.0
            for assignment in completed_assignments:
                results = self.expert_database.get_review_results(assignment.content_id)
                for result in results:
                    if result.expert_id == expert_id:
                        total_quality += result.quality_score
            avg_quality = total_quality / len(completed_assignments)
        
        return {
            "expert_id": expert_id,
            "name": expert.name,
            "organization": expert.organization,
            "title": expert.title,
            "categories": expert.categories,
            "expertise_areas": expert.expertise_areas,
            "current_workload": expert.current_workload,
            "max_workload": expert.max_workload,
            "rating": expert.rating,
            "total_reviews": len(completed_assignments),
            "average_quality": avg_quality,
            "availability": expert.availability
        }
    
    def add_sample_data(self):
        """添加示例数据"""
        # 添加示例专家
        experts = [
            Expert(
                id="expert_001", name="李教授", email="li@university.edu",
                organization="清华大学", title="计算机科学教授",
                categories=[ExpertCategory.ACADEMIC.value, ExpertCategory.METHODOLOGY.value],
                expertise_areas=["形式化方法", "软件工程", "定理证明"],
                rating=4.8, review_count=50
            ),
            Expert(
                id="expert_002", name="王工程师", email="wang@tech.com",
                organization="阿里巴巴", title="高级架构师",
                categories=[ExpertCategory.INDUSTRY.value, ExpertCategory.DOMAIN.value],
                expertise_areas=["云原生", "微服务", "分布式系统"],
                rating=4.6, review_count=30
            ),
            Expert(
                id="expert_003", name="张研究员", email="zhang@research.org",
                organization="中科院", title="研究员",
                categories=[ExpertCategory.ACADEMIC.value, ExpertCategory.DOMAIN.value],
                expertise_areas=["人工智能", "机器学习", "深度学习"],
                rating=4.9, review_count=40
            )
        ]
        
        for expert in experts:
            self.add_expert(expert)
        
        # 添加示例内容
        content_items = [
            ContentItem(
                id="content_001", title="形式化验证方法研究",
                content_type="research", category="formal_methods",
                author_id="author_001", current_quality_score=0.0
            ),
            ContentItem(
                id="content_002", title="云原生架构设计指南",
                content_type="document", category="cloud_native",
                author_id="author_002", current_quality_score=0.0
            )
        ]
        
        for content in content_items:
            self.add_content_for_review(content)
        
        logger.info("示例数据添加完成")

def main():
    """主函数"""
    # 创建专家评审网络
    review_network = ExpertReviewNetwork()
    
    # 添加示例数据
    review_network.add_sample_data()
    
    # 分配评审任务
    assignments = review_network.assign_review(
        content_id="content_001",
        review_type="research",
        priority=ReviewPriority.HIGH,
        deadline_days=10
    )
    
    print(f"分配了 {len(assignments)} 个评审任务")
    
    # 模拟评审过程
    if assignments:
        assignment = assignments[0]
        
        # 开始评审
        review_network.start_review(assignment.id, assignment.expert_id)
        
        # 提交评审结果
        success = review_network.submit_review(
            assignment_id=assignment.id,
            expert_id=assignment.expert_id,
            quality_score=85.0,
            technical_accuracy=90.0,
            completeness=80.0,
            clarity=85.0,
            comments="这是一篇高质量的研究论文，理论基础扎实，方法创新性强。",
            recommendations=["建议增加更多实验验证", "可以进一步扩展应用场景"]
        )
        
        if success:
            print("评审结果提交成功")
            
            # 获取专家统计信息
            stats = review_network.get_expert_statistics(assignment.expert_id)
            print(f"专家统计信息: {stats}")

if __name__ == "__main__":
    main()
