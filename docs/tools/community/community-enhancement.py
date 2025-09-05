#!/usr/bin/env python3
"""
社区功能增强系统
提供社区管理、贡献跟踪、治理机制等功能
"""

import json
import datetime
import hashlib
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart


class ContributionType(Enum):
    """贡献类型"""
    CODE = "code"
    DOCUMENTATION = "documentation"
    BUG_REPORT = "bug_report"
    FEATURE_REQUEST = "feature_request"
    TRANSLATION = "translation"
    TESTING = "testing"
    REVIEW = "review"
    MENTORING = "mentoring"
    COMMUNITY = "community"


class UserRole(Enum):
    """用户角色"""
    CONTRIBUTOR = "contributor"
    MAINTAINER = "maintainer"
    REVIEWER = "reviewer"
    ADMIN = "admin"
    MENTOR = "mentor"


@dataclass
class User:
    """用户信息"""
    user_id: str
    username: str
    email: str
    name: str
    role: UserRole
    join_date: datetime.datetime
    last_active: datetime.datetime
    contributions: List[str]
    reputation: int
    badges: List[str]
    timezone: str
    bio: str
    social_links: Dict[str, str]


@dataclass
class Contribution:
    """贡献记录"""
    contribution_id: str
    user_id: str
    type: ContributionType
    title: str
    description: str
    status: str  # pending, approved, rejected, merged
    created_at: datetime.datetime
    updated_at: datetime.datetime
    reviewers: List[str]
    comments: List[Dict[str, Any]]
    metrics: Dict[str, Any]
    tags: List[str]


@dataclass
class GovernanceRule:
    """治理规则"""
    rule_id: str
    name: str
    description: str
    category: str
    priority: int
    conditions: List[str]
    actions: List[str]
    created_at: datetime.datetime
    updated_at: datetime.datetime
    active: bool


class CommunityEnhancement:
    """社区功能增强系统"""
    
    def __init__(self, config_path: str = "community-config.json"):
        self.config = self.load_config(config_path)
        self.users: Dict[str, User] = {}
        self.contributions: Dict[str, Contribution] = {}
        self.governance_rules: Dict[str, GovernanceRule] = {}
        self.notifications: List[Dict[str, Any]] = []
    
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
            "community": {
                "name": "正式验证框架社区",
                "description": "致力于推动正式验证技术发展的开放社区",
                "website": "https://community.formal-framework.org",
                "repository": "https://github.com/formal-framework/community"
            },
            "roles": {
                "contributor": {
                    "permissions": ["create_issue", "submit_pr", "comment"],
                    "requirements": ["github_account", "signed_cla"]
                },
                "reviewer": {
                    "permissions": ["review_pr", "approve_pr", "merge_pr"],
                    "requirements": ["contributor", "technical_expertise", "community_trust"]
                },
                "maintainer": {
                    "permissions": ["manage_releases", "manage_issues", "manage_milestones"],
                    "requirements": ["reviewer", "long_term_commitment", "leadership_skills"]
                },
                "admin": {
                    "permissions": ["manage_users", "manage_roles", "system_config"],
                    "requirements": ["maintainer", "security_clearance", "admin_approval"]
                }
            },
            "contribution_types": {
                "code": {
                    "weight": 10,
                    "description": "代码贡献",
                    "requirements": ["unit_tests", "documentation", "code_review"]
                },
                "documentation": {
                    "weight": 5,
                    "description": "文档贡献",
                    "requirements": ["accuracy", "clarity", "completeness"]
                },
                "bug_report": {
                    "weight": 3,
                    "description": "Bug报告",
                    "requirements": ["reproducible", "detailed_description", "environment_info"]
                },
                "feature_request": {
                    "weight": 2,
                    "description": "功能请求",
                    "requirements": ["use_case", "rationale", "implementation_ideas"]
                }
            },
            "governance": {
                "decision_making": {
                    "consensus_threshold": 0.75,
                    "voting_period_days": 7,
                    "quorum_percentage": 0.3
                },
                "code_of_conduct": {
                    "enforcement": "strict",
                    "reporting_process": "confidential",
                    "consequences": ["warning", "temporary_ban", "permanent_ban"]
                }
            }
        }
    
    def register_user(self, user_id: str, username: str, email: str, 
                     name: str, timezone: str = "UTC") -> User:
        """注册用户"""
        if user_id in self.users:
            raise ValueError(f"用户 {user_id} 已存在")
        
        user = User(
            user_id=user_id,
            username=username,
            email=email,
            name=name,
            role=UserRole.CONTRIBUTOR,
            join_date=datetime.datetime.now(),
            last_active=datetime.datetime.now(),
            contributions=[],
            reputation=0,
            badges=[],
            timezone=timezone,
            bio="",
            social_links={}
        )
        
        self.users[user_id] = user
        self._send_welcome_email(user)
        return user
    
    def submit_contribution(self, user_id: str, contribution_type: ContributionType,
                          title: str, description: str, tags: List[str] = None) -> str:
        """提交贡献"""
        if user_id not in self.users:
            raise ValueError(f"用户 {user_id} 不存在")
        
        contribution_id = self._generate_contribution_id(user_id, contribution_type)
        
        contribution = Contribution(
            contribution_id=contribution_id,
            user_id=user_id,
            type=contribution_type,
            title=title,
            description=description,
            status="pending",
            created_at=datetime.datetime.now(),
            updated_at=datetime.datetime.now(),
            reviewers=[],
            comments=[],
            metrics={},
            tags=tags or []
        )
        
        self.contributions[contribution_id] = contribution
        self.users[user_id].contributions.append(contribution_id)
        
        # 自动分配审查者
        self._assign_reviewers(contribution)
        
        # 发送通知
        self._notify_contribution_submitted(contribution)
        
        return contribution_id
    
    def review_contribution(self, contribution_id: str, reviewer_id: str,
                          decision: str, comments: str) -> bool:
        """审查贡献"""
        if contribution_id not in self.contributions:
            return False
        
        if reviewer_id not in self.users:
            return False
        
        contribution = self.contributions[contribution_id]
        
        # 检查审查者权限
        if not self._can_review(reviewer_id, contribution):
            return False
        
        # 添加审查评论
        review_comment = {
            "reviewer_id": reviewer_id,
            "decision": decision,
            "comments": comments,
            "timestamp": datetime.datetime.now().isoformat()
        }
        
        contribution.comments.append(review_comment)
        contribution.updated_at = datetime.datetime.now()
        
        # 如果审查者不在列表中，添加进去
        if reviewer_id not in contribution.reviewers:
            contribution.reviewers.append(reviewer_id)
        
        # 检查是否需要更新状态
        self._update_contribution_status(contribution)
        
        # 发送通知
        self._notify_contribution_reviewed(contribution, reviewer_id, decision)
        
        return True
    
    def _can_review(self, reviewer_id: str, contribution: Contribution) -> bool:
        """检查是否可以审查"""
        user = self.users[reviewer_id]
        
        # 检查角色权限
        if user.role in [UserRole.REVIEWER, UserRole.MAINTAINER, UserRole.ADMIN]:
            return True
        
        # 检查是否是贡献者本人
        if reviewer_id == contribution.user_id:
            return False
        
        # 检查是否有足够的声誉
        if user.reputation >= 100:
            return True
        
        return False
    
    def _update_contribution_status(self, contribution: Contribution):
        """更新贡献状态"""
        if contribution.status != "pending":
            return
        
        # 统计审查结果
        approvals = sum(1 for comment in contribution.comments 
                       if comment.get("decision") == "approved")
        rejections = sum(1 for comment in contribution.comments 
                        if comment.get("decision") == "rejected")
        
        total_reviews = len(contribution.comments)
        
        if total_reviews >= 2:  # 至少需要2个审查
            if approvals >= 2:
                contribution.status = "approved"
                self._award_contribution_points(contribution)
            elif rejections >= 1:
                contribution.status = "rejected"
    
    def _award_contribution_points(self, contribution: Contribution):
        """奖励贡献积分"""
        user = self.users[contribution.user_id]
        contribution_type_config = self.config["contribution_types"].get(
            contribution.type.value, {}
        )
        
        points = contribution_type_config.get("weight", 1)
        user.reputation += points
        
        # 检查是否获得新徽章
        self._check_badges(user)
    
    def _check_badges(self, user: User):
        """检查用户徽章"""
        new_badges = []
        
        # 首次贡献徽章
        if len(user.contributions) == 1 and "first_contribution" not in user.badges:
            new_badges.append("first_contribution")
        
        # 活跃贡献者徽章
        if len(user.contributions) >= 10 and "active_contributor" not in user.badges:
            new_badges.append("active_contributor")
        
        # 高声誉徽章
        if user.reputation >= 500 and "high_reputation" not in user.badges:
            new_badges.append("high_reputation")
        
        # 审查者徽章
        review_count = sum(1 for contrib in self.contributions.values() 
                          if user.user_id in contrib.reviewers)
        if review_count >= 20 and "reviewer" not in user.badges:
            new_badges.append("reviewer")
        
        user.badges.extend(new_badges)
        
        # 发送徽章通知
        for badge in new_badges:
            self._notify_badge_earned(user, badge)
    
    def create_governance_rule(self, name: str, description: str, category: str,
                             conditions: List[str], actions: List[str]) -> str:
        """创建治理规则"""
        rule_id = self._generate_rule_id(name)
        
        rule = GovernanceRule(
            rule_id=rule_id,
            name=name,
            description=description,
            category=category,
            priority=1,
            conditions=conditions,
            actions=actions,
            created_at=datetime.datetime.now(),
            updated_at=datetime.datetime.now(),
            active=True
        )
        
        self.governance_rules[rule_id] = rule
        return rule_id
    
    def apply_governance_rules(self, event_type: str, event_data: Dict[str, Any]):
        """应用治理规则"""
        for rule in self.governance_rules.values():
            if not rule.active:
                continue
            
            if self._rule_matches(rule, event_type, event_data):
                self._execute_rule_actions(rule, event_data)
    
    def _rule_matches(self, rule: GovernanceRule, event_type: str, 
                     event_data: Dict[str, Any]) -> bool:
        """检查规则是否匹配"""
        for condition in rule.conditions:
            if not self._evaluate_condition(condition, event_type, event_data):
                return False
        return True
    
    def _evaluate_condition(self, condition: str, event_type: str, 
                           event_data: Dict[str, Any]) -> bool:
        """评估条件"""
        # 简化的条件评估逻辑
        if "event_type" in condition:
            return event_type in condition
        elif "user_role" in condition:
            user_id = event_data.get("user_id")
            if user_id and user_id in self.users:
                return self.users[user_id].role.value in condition
        return True
    
    def _execute_rule_actions(self, rule: GovernanceRule, event_data: Dict[str, Any]):
        """执行规则动作"""
        for action in rule.actions:
            if action == "send_notification":
                self._send_governance_notification(rule, event_data)
            elif action == "escalate_to_admin":
                self._escalate_to_admin(rule, event_data)
            elif action == "auto_approve":
                self._auto_approve_contribution(event_data)
    
    def get_community_stats(self) -> Dict[str, Any]:
        """获取社区统计信息"""
        total_users = len(self.users)
        active_users = len([u for u in self.users.values() 
                           if (datetime.datetime.now() - u.last_active).days <= 30])
        
        total_contributions = len(self.contributions)
        pending_contributions = len([c for c in self.contributions.values() 
                                   if c.status == "pending"])
        
        # 按类型统计贡献
        contribution_by_type = {}
        for contrib in self.contributions.values():
            contrib_type = contrib.type.value
            contribution_by_type[contrib_type] = contribution_by_type.get(contrib_type, 0) + 1
        
        # 按角色统计用户
        users_by_role = {}
        for user in self.users.values():
            role = user.role.value
            users_by_role[role] = users_by_role.get(role, 0) + 1
        
        return {
            "total_users": total_users,
            "active_users": active_users,
            "total_contributions": total_contributions,
            "pending_contributions": pending_contributions,
            "contribution_by_type": contribution_by_type,
            "users_by_role": users_by_role,
            "governance_rules": len(self.governance_rules),
            "active_rules": len([r for r in self.governance_rules.values() if r.active])
        }
    
    def _generate_contribution_id(self, user_id: str, contrib_type: ContributionType) -> str:
        """生成贡献ID"""
        timestamp = datetime.datetime.now().isoformat()
        data = f"{user_id}_{contrib_type.value}_{timestamp}"
        return hashlib.md5(data.encode()).hexdigest()[:12]
    
    def _generate_rule_id(self, name: str) -> str:
        """生成规则ID"""
        data = f"rule_{name}_{datetime.datetime.now().isoformat()}"
        return hashlib.md5(data.encode()).hexdigest()[:12]
    
    def _assign_reviewers(self, contribution: Contribution):
        """自动分配审查者"""
        # 根据贡献类型和用户角色分配审查者
        potential_reviewers = []
        
        for user in self.users.values():
            if user.role in [UserRole.REVIEWER, UserRole.MAINTAINER, UserRole.ADMIN]:
                if user.user_id != contribution.user_id:
                    potential_reviewers.append(user.user_id)
        
        # 选择前2个审查者
        contribution.reviewers = potential_reviewers[:2]
    
    def _send_welcome_email(self, user: User):
        """发送欢迎邮件"""
        # 这里应该实现实际的邮件发送逻辑
        print(f"发送欢迎邮件给 {user.email}")
    
    def _notify_contribution_submitted(self, contribution: Contribution):
        """通知贡献提交"""
        # 通知审查者
        for reviewer_id in contribution.reviewers:
            if reviewer_id in self.users:
                reviewer = self.users[reviewer_id]
                print(f"通知审查者 {reviewer.name}: 新的贡献需要审查")
    
    def _notify_contribution_reviewed(self, contribution: Contribution, 
                                    reviewer_id: str, decision: str):
        """通知贡献审查结果"""
        contributor = self.users[contribution.user_id]
        print(f"通知贡献者 {contributor.name}: 贡献审查结果 - {decision}")
    
    def _notify_badge_earned(self, user: User, badge: str):
        """通知获得徽章"""
        print(f"恭喜 {user.name} 获得徽章: {badge}")
    
    def _send_governance_notification(self, rule: GovernanceRule, event_data: Dict[str, Any]):
        """发送治理通知"""
        print(f"治理规则触发: {rule.name}")
    
    def _escalate_to_admin(self, rule: GovernanceRule, event_data: Dict[str, Any]):
        """升级到管理员"""
        print(f"升级到管理员: {rule.name}")
    
    def _auto_approve_contribution(self, event_data: Dict[str, Any]):
        """自动批准贡献"""
        print("自动批准贡献")
    
    def save_data(self, filepath: str = "community-data.json"):
        """保存数据"""
        data = {
            "users": {uid: asdict(user) for uid, user in self.users.items()},
            "contributions": {cid: asdict(contrib) for cid, contrib in self.contributions.items()},
            "governance_rules": {rid: asdict(rule) for rid, rule in self.governance_rules.items()},
            "timestamp": datetime.datetime.now().isoformat()
        }
        
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False, default=str)


def main():
    """主函数 - 演示社区增强系统"""
    community = CommunityEnhancement()
    
    print("=== 正式验证框架社区增强系统演示 ===")
    
    # 注册用户
    user1 = community.register_user("user001", "alice", "alice@example.com", "Alice Smith")
    user2 = community.register_user("user002", "bob", "bob@example.com", "Bob Johnson")
    user3 = community.register_user("user003", "charlie", "charlie@example.com", "Charlie Brown")
    
    print(f"注册用户: {user1.name}, {user2.name}, {user3.name}")
    
    # 设置用户角色
    user2.role = UserRole.REVIEWER
    user3.role = UserRole.MAINTAINER
    
    # 提交贡献
    contrib1 = community.submit_contribution(
        "user001", 
        ContributionType.CODE, 
        "添加新的验证算法",
        "实现了基于SAT求解器的验证算法",
        ["algorithm", "sat-solver", "verification"]
    )
    
    contrib2 = community.submit_contribution(
        "user001",
        ContributionType.DOCUMENTATION,
        "更新API文档",
        "更新了所有API接口的文档",
        ["documentation", "api", "update"]
    )
    
    print(f"提交贡献: {contrib1}, {contrib2}")
    
    # 审查贡献
    community.review_contribution(contrib1, "user002", "approved", "代码质量很好，建议合并")
    community.review_contribution(contrib1, "user003", "approved", "算法实现正确，测试覆盖充分")
    
    community.review_contribution(contrib2, "user002", "approved", "文档清晰完整")
    
    # 创建治理规则
    rule1 = community.create_governance_rule(
        "自动批准文档贡献",
        "对于高质量的文档贡献自动批准",
        "automation",
        ["contribution_type == documentation", "quality_score >= 8"],
        ["auto_approve"]
    )
    
    print(f"创建治理规则: {rule1}")
    
    # 获取社区统计
    stats = community.get_community_stats()
    print(f"\n社区统计:")
    print(f"  总用户数: {stats['total_users']}")
    print(f"  活跃用户数: {stats['active_users']}")
    print(f"  总贡献数: {stats['total_contributions']}")
    print(f"  待审查贡献数: {stats['pending_contributions']}")
    print(f"  贡献类型分布: {stats['contribution_by_type']}")
    print(f"  用户角色分布: {stats['users_by_role']}")
    
    # 保存数据
    community.save_data()
    print(f"\n数据已保存到 community-data.json")


if __name__ == "__main__":
    main()
