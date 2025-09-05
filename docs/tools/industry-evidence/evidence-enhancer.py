#!/usr/bin/env python3
"""
行业证据条目实证化增强系统
自动收集、验证和链接外部证据来源
"""

import json
import requests
import hashlib
import datetime
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
import re
from urllib.parse import urlparse
import time


class EvidenceType(Enum):
    """证据类型"""
    ACADEMIC_PAPER = "academic_paper"
    INDUSTRY_REPORT = "industry_report"
    STANDARD_DOCUMENT = "standard_document"
    CASE_STUDY = "case_study"
    TECHNICAL_DOCUMENTATION = "technical_documentation"
    BENCHMARK_RESULT = "benchmark_result"
    CERTIFICATION = "certification"
    WHITE_PAPER = "white_paper"


class EvidenceSource(Enum):
    """证据来源"""
    IEEE = "ieee"
    ACM = "acm"
    NIST = "nist"
    ISO = "iso"
    INDUSTRY = "industry"
    GITHUB = "github"
    RESEARCH_GATE = "research_gate"
    ARXIV = "arxiv"
    GOOGLE_SCHOLAR = "google_scholar"


@dataclass
class EvidenceEntry:
    """证据条目"""
    evidence_id: str
    title: str
    evidence_type: EvidenceType
    source: EvidenceSource
    url: str
    doi: Optional[str]
    authors: List[str]
    publication_date: datetime.datetime
    abstract: str
    keywords: List[str]
    relevance_score: float
    verification_status: str
    metadata: Dict[str, Any]


@dataclass
class IndustryCapability:
    """行业能力"""
    capability_id: str
    industry: str
    domain: str
    capability_name: str
    description: str
    required_evidence_count: int
    current_evidence_count: int
    evidence_entries: List[str]
    coverage_score: float


class EvidenceEnhancer:
    """证据增强系统"""
    
    def __init__(self, config_path: str = "evidence-config.json"):
        self.config = self.load_config(config_path)
        self.evidence_entries: Dict[str, EvidenceEntry] = {}
        self.industry_capabilities: Dict[str, IndustryCapability] = {}
        self.search_apis = self._initialize_search_apis()
    
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
            "search_apis": {
                "ieee": {
                    "base_url": "https://ieeexploreapi.ieee.org/api/v1/search/articles",
                    "api_key": "your_ieee_api_key",
                    "enabled": True
                },
                "arxiv": {
                    "base_url": "http://export.arxiv.org/api/query",
                    "enabled": True
                },
                "crossref": {
                    "base_url": "https://api.crossref.org/works",
                    "enabled": True
                },
                "github": {
                    "base_url": "https://api.github.com/search/repositories",
                    "token": "your_github_token",
                    "enabled": True
                }
            },
            "industries": {
                "cloud_native": {
                    "domains": ["kubernetes", "microservices", "containerization", "devops"],
                    "required_evidence_per_domain": 3,
                    "priority_keywords": ["kubernetes", "docker", "istio", "prometheus", "grafana"]
                },
                "finance": {
                    "domains": ["open_banking", "payment_systems", "risk_management", "compliance"],
                    "required_evidence_per_domain": 3,
                    "priority_keywords": ["open_banking", "pci_dss", "iso_20022", "fraud_detection"]
                },
                "iot": {
                    "domains": ["mqtt", "device_management", "edge_computing", "security"],
                    "required_evidence_per_domain": 3,
                    "priority_keywords": ["mqtt", "coap", "edge_computing", "iot_security"]
                },
                "ai_infrastructure": {
                    "domains": ["mlops", "model_serving", "data_pipelines", "model_governance"],
                    "required_evidence_per_domain": 3,
                    "priority_keywords": ["tensorflow", "pytorch", "mlops", "model_serving"]
                },
                "web3": {
                    "domains": ["blockchain", "smart_contracts", "defi", "nft"],
                    "required_evidence_per_domain": 3,
                    "priority_keywords": ["ethereum", "solidity", "defi", "smart_contracts"]
                }
            },
            "quality_thresholds": {
                "min_relevance_score": 0.7,
                "min_publication_year": 2018,
                "max_publication_year": 2024,
                "min_abstract_length": 100,
                "required_verification_sources": 2
            }
        }
    
    def _initialize_search_apis(self) -> Dict[str, Any]:
        """初始化搜索API"""
        return {
            "ieee": self._create_ieee_searcher(),
            "arxiv": self._create_arxiv_searcher(),
            "crossref": self._create_crossref_searcher(),
            "github": self._create_github_searcher()
        }
    
    def _create_ieee_searcher(self):
        """创建IEEE搜索器"""
        def search_ieee(query: str, max_results: int = 10) -> List[Dict[str, Any]]:
            try:
                api_key = self.config["search_apis"]["ieee"]["api_key"]
                base_url = self.config["search_apis"]["ieee"]["base_url"]
                
                params = {
                    "apikey": api_key,
                    "format": "json",
                    "max_records": max_results,
                    "querytext": query,
                    "sort_field": "relevance",
                    "sort_order": "desc"
                }
                
                response = requests.get(base_url, params=params, timeout=30)
                if response.status_code == 200:
                    data = response.json()
                    return data.get("articles", [])
                else:
                    print(f"IEEE API error: {response.status_code}")
                    return []
            except Exception as e:
                print(f"IEEE search error: {str(e)}")
                return []
        
        return search_ieee
    
    def _create_arxiv_searcher(self):
        """创建ArXiv搜索器"""
        def search_arxiv(query: str, max_results: int = 10) -> List[Dict[str, Any]]:
            try:
                base_url = self.config["search_apis"]["arxiv"]["base_url"]
                
                params = {
                    "search_query": f"all:{query}",
                    "start": 0,
                    "max_results": max_results,
                    "sortBy": "relevance",
                    "sortOrder": "descending"
                }
                
                response = requests.get(base_url, params=params, timeout=30)
                if response.status_code == 200:
                    # 解析ArXiv XML响应
                    import xml.etree.ElementTree as ET
                    root = ET.fromstring(response.content)
                    
                    entries = []
                    for entry in root.findall("{http://www.w3.org/2005/Atom}entry"):
                        entry_data = {
                            "title": entry.find("{http://www.w3.org/2005/Atom}title").text,
                            "summary": entry.find("{http://www.w3.org/2005/Atom}summary").text,
                            "published": entry.find("{http://www.w3.org/2005/Atom}published").text,
                            "id": entry.find("{http://www.w3.org/2005/Atom}id").text,
                            "authors": [author.find("{http://www.w3.org/2005/Atom}name").text 
                                      for author in entry.findall("{http://www.w3.org/2005/Atom}author")]
                        }
                        entries.append(entry_data)
                    
                    return entries
                else:
                    print(f"ArXiv API error: {response.status_code}")
                    return []
            except Exception as e:
                print(f"ArXiv search error: {str(e)}")
                return []
        
        return search_arxiv
    
    def _create_crossref_searcher(self):
        """创建CrossRef搜索器"""
        def search_crossref(query: str, max_results: int = 10) -> List[Dict[str, Any]]:
            try:
                base_url = self.config["search_apis"]["crossref"]["base_url"]
                
                params = {
                    "query": query,
                    "rows": max_results,
                    "sort": "relevance",
                    "order": "desc"
                }
                
                response = requests.get(base_url, params=params, timeout=30)
                if response.status_code == 200:
                    data = response.json()
                    return data.get("message", {}).get("items", [])
                else:
                    print(f"CrossRef API error: {response.status_code}")
                    return []
            except Exception as e:
                print(f"CrossRef search error: {str(e)}")
                return []
        
        return search_crossref
    
    def _create_github_searcher(self):
        """创建GitHub搜索器"""
        def search_github(query: str, max_results: int = 10) -> List[Dict[str, Any]]:
            try:
                base_url = self.config["search_apis"]["github"]["base_url"]
                token = self.config["search_apis"]["github"].get("token")
                
                headers = {}
                if token:
                    headers["Authorization"] = f"token {token}"
                
                params = {
                    "q": query,
                    "sort": "stars",
                    "order": "desc",
                    "per_page": max_results
                }
                
                response = requests.get(base_url, params=params, headers=headers, timeout=30)
                if response.status_code == 200:
                    data = response.json()
                    return data.get("items", [])
                else:
                    print(f"GitHub API error: {response.status_code}")
                    return []
            except Exception as e:
                print(f"GitHub search error: {str(e)}")
                return []
        
        return search_github
    
    def search_evidence(self, query: str, industry: str, domain: str) -> List[EvidenceEntry]:
        """搜索证据"""
        print(f"搜索证据: {query} (行业: {industry}, 领域: {domain})")
        
        evidence_entries = []
        
        # 从多个来源搜索
        for source_name, searcher in self.search_apis.items():
            if not self.config["search_apis"][source_name].get("enabled", True):
                continue
            
            try:
                results = searcher(query, max_results=5)
                
                for result in results:
                    evidence_entry = self._parse_search_result(result, source_name, industry, domain)
                    if evidence_entry and self._validate_evidence(evidence_entry):
                        evidence_entries.append(evidence_entry)
                        self.evidence_entries[evidence_entry.evidence_id] = evidence_entry
                
                # 避免API限制
                time.sleep(1)
                
            except Exception as e:
                print(f"搜索 {source_name} 时出错: {str(e)}")
        
        return evidence_entries
    
    def _parse_search_result(self, result: Dict[str, Any], source: str, 
                           industry: str, domain: str) -> Optional[EvidenceEntry]:
        """解析搜索结果"""
        try:
            # 生成证据ID
            evidence_id = self._generate_evidence_id(result, source)
            
            # 提取基本信息
            title = result.get("title", "").strip()
            if not title:
                return None
            
            # 提取摘要
            abstract = result.get("summary", result.get("abstract", "")).strip()
            if len(abstract) < self.config["quality_thresholds"]["min_abstract_length"]:
                return None
            
            # 提取作者
            authors = []
            if "authors" in result:
                if isinstance(result["authors"], list):
                    authors = [author.get("name", str(author)) for author in result["authors"]]
                else:
                    authors = [str(result["authors"])]
            
            # 提取发布日期
            publication_date = self._parse_publication_date(result)
            if not publication_date:
                return None
            
            # 检查年份范围
            year = publication_date.year
            min_year = self.config["quality_thresholds"]["min_publication_year"]
            max_year = self.config["quality_thresholds"]["max_publication_year"]
            
            if year < min_year or year > max_year:
                return None
            
            # 提取DOI
            doi = result.get("doi", result.get("DOI"))
            
            # 提取URL
            url = result.get("url", result.get("link", result.get("html_url", "")))
            
            # 计算相关性分数
            relevance_score = self._calculate_relevance_score(result, industry, domain)
            
            # 提取关键词
            keywords = self._extract_keywords(result, industry, domain)
            
            evidence_entry = EvidenceEntry(
                evidence_id=evidence_id,
                title=title,
                evidence_type=self._determine_evidence_type(result, source),
                source=EvidenceSource(source.upper()) if hasattr(EvidenceSource, source.upper()) else EvidenceSource.INDUSTRY,
                url=url,
                doi=doi,
                authors=authors,
                publication_date=publication_date,
                abstract=abstract,
                keywords=keywords,
                relevance_score=relevance_score,
                verification_status="pending",
                metadata={
                    "industry": industry,
                    "domain": domain,
                    "source_data": result,
                    "search_timestamp": datetime.datetime.now().isoformat()
                }
            )
            
            return evidence_entry
            
        except Exception as e:
            print(f"解析搜索结果时出错: {str(e)}")
            return None
    
    def _generate_evidence_id(self, result: Dict[str, Any], source: str) -> str:
        """生成证据ID"""
        # 使用标题和来源生成唯一ID
        title = result.get("title", "")
        url = result.get("url", result.get("link", ""))
        
        data = f"{source}_{title}_{url}"
        return hashlib.md5(data.encode()).hexdigest()[:16]
    
    def _parse_publication_date(self, result: Dict[str, Any]) -> Optional[datetime.datetime]:
        """解析发布日期"""
        date_fields = ["published", "publication_date", "date", "created_at", "updated_at"]
        
        for field in date_fields:
            if field in result:
                try:
                    date_str = result[field]
                    if isinstance(date_str, str):
                        # 尝试多种日期格式
                        formats = [
                            "%Y-%m-%d",
                            "%Y-%m-%dT%H:%M:%S",
                            "%Y-%m-%dT%H:%M:%SZ",
                            "%Y-%m-%dT%H:%M:%S.%fZ",
                            "%Y-%m-%d %H:%M:%S"
                        ]
                        
                        for fmt in formats:
                            try:
                                return datetime.datetime.strptime(date_str, fmt)
                            except ValueError:
                                continue
                except:
                    continue
        
        return None
    
    def _calculate_relevance_score(self, result: Dict[str, Any], industry: str, domain: str) -> float:
        """计算相关性分数"""
        score = 0.0
        
        # 基于标题的相关性
        title = result.get("title", "").lower()
        abstract = result.get("summary", result.get("abstract", "")).lower()
        text = f"{title} {abstract}"
        
        # 获取行业关键词
        industry_config = self.config["industries"].get(industry, {})
        priority_keywords = industry_config.get("priority_keywords", [])
        domain_keywords = industry_config.get("domains", [])
        
        # 计算关键词匹配分数
        all_keywords = priority_keywords + domain_keywords
        
        for keyword in all_keywords:
            keyword_lower = keyword.lower()
            if keyword_lower in text:
                if keyword in priority_keywords:
                    score += 0.1  # 优先级关键词权重更高
                else:
                    score += 0.05  # 普通关键词权重
        
        # 基于来源的分数调整
        source = result.get("source", "")
        if "ieee" in source.lower():
            score += 0.2
        elif "arxiv" in source.lower():
            score += 0.15
        elif "github" in source.lower():
            score += 0.1
        
        # 基于引用数的分数调整（如果有）
        citations = result.get("citations", result.get("citation_count", 0))
        if citations > 0:
            score += min(0.2, citations / 100)  # 最多增加0.2分
        
        return min(1.0, score)  # 确保分数不超过1.0
    
    def _extract_keywords(self, result: Dict[str, Any], industry: str, domain: str) -> List[str]:
        """提取关键词"""
        keywords = []
        
        # 从标题和摘要中提取关键词
        title = result.get("title", "")
        abstract = result.get("summary", result.get("abstract", ""))
        
        # 简单的关键词提取（实际应用中可以使用更复杂的NLP技术）
        text = f"{title} {abstract}".lower()
        
        # 预定义的技术关键词
        tech_keywords = [
            "formal verification", "model checking", "theorem proving",
            "kubernetes", "docker", "microservices", "api", "security",
            "blockchain", "smart contracts", "machine learning", "ai",
            "iot", "mqtt", "edge computing", "cloud native"
        ]
        
        for keyword in tech_keywords:
            if keyword in text:
                keywords.append(keyword)
        
        # 添加行业特定关键词
        industry_config = self.config["industries"].get(industry, {})
        domain_keywords = industry_config.get("domains", [])
        keywords.extend(domain_keywords)
        
        return list(set(keywords))  # 去重
    
    def _determine_evidence_type(self, result: Dict[str, Any], source: str) -> EvidenceType:
        """确定证据类型"""
        title = result.get("title", "").lower()
        abstract = result.get("summary", result.get("abstract", "")).lower()
        text = f"{title} {abstract}"
        
        if "paper" in text or "journal" in text or "conference" in text:
            return EvidenceType.ACADEMIC_PAPER
        elif "report" in text or "study" in text:
            return EvidenceType.INDUSTRY_REPORT
        elif "standard" in text or "specification" in text:
            return EvidenceType.STANDARD_DOCUMENT
        elif "case study" in text or "implementation" in text:
            return EvidenceType.CASE_STUDY
        elif "documentation" in text or "guide" in text:
            return EvidenceType.TECHNICAL_DOCUMENTATION
        elif "benchmark" in text or "performance" in text:
            return EvidenceType.BENCHMARK_RESULT
        elif "certification" in text or "compliance" in text:
            return EvidenceType.CERTIFICATION
        else:
            return EvidenceType.WHITE_PAPER
    
    def _validate_evidence(self, evidence: EvidenceEntry) -> bool:
        """验证证据质量"""
        # 检查最小相关性分数
        min_score = self.config["quality_thresholds"]["min_relevance_score"]
        if evidence.relevance_score < min_score:
            return False
        
        # 检查摘要长度
        min_abstract_length = self.config["quality_thresholds"]["min_abstract_length"]
        if len(evidence.abstract) < min_abstract_length:
            return False
        
        # 检查是否有有效的URL或DOI
        if not evidence.url and not evidence.doi:
            return False
        
        return True
    
    def enhance_industry_capabilities(self) -> Dict[str, IndustryCapability]:
        """增强行业能力证据"""
        print("开始增强行业能力证据...")
        
        for industry, industry_config in self.config["industries"].items():
            print(f"\n处理行业: {industry}")
            
            domains = industry_config.get("domains", [])
            required_evidence_per_domain = industry_config.get("required_evidence_per_domain", 3)
            
            for domain in domains:
                print(f"  处理领域: {domain}")
                
                # 构建搜索查询
                query = f"{industry} {domain} formal verification"
                
                # 搜索证据
                evidence_entries = self.search_evidence(query, industry, domain)
                
                # 创建或更新行业能力
                capability_id = f"{industry}_{domain}"
                
                if capability_id not in self.industry_capabilities:
                    capability = IndustryCapability(
                        capability_id=capability_id,
                        industry=industry,
                        domain=domain,
                        capability_name=f"{industry.title()} {domain.title()}",
                        description=f"Formal verification capabilities for {domain} in {industry}",
                        required_evidence_count=required_evidence_per_domain,
                        current_evidence_count=0,
                        evidence_entries=[],
                        coverage_score=0.0
                    )
                    self.industry_capabilities[capability_id] = capability
                
                capability = self.industry_capabilities[capability_id]
                
                # 添加证据条目
                for evidence in evidence_entries:
                    if evidence.evidence_id not in capability.evidence_entries:
                        capability.evidence_entries.append(evidence.evidence_id)
                        capability.current_evidence_count += 1
                
                # 计算覆盖分数
                capability.coverage_score = min(1.0, capability.current_evidence_count / capability.required_evidence_count)
                
                print(f"    找到 {len(evidence_entries)} 个证据条目")
                print(f"    覆盖分数: {capability.coverage_score:.2%}")
        
        return self.industry_capabilities
    
    def generate_evidence_report(self) -> str:
        """生成证据报告"""
        report = f"""
# 行业证据实证化报告

## 概览
- 总证据条目数: {len(self.evidence_entries)}
- 行业能力数: {len(self.industry_capabilities)}
- 平均覆盖分数: {sum(c.coverage_score for c in self.industry_capabilities.values()) / len(self.industry_capabilities):.2%}

## 行业能力详情

"""
        
        for capability in self.industry_capabilities.values():
            report += f"""
### {capability.capability_name}
- **行业**: {capability.industry}
- **领域**: {capability.domain}
- **当前证据数**: {capability.current_evidence_count}/{capability.required_evidence_count}
- **覆盖分数**: {capability.coverage_score:.2%}
- **状态**: {'✅ 完成' if capability.coverage_score >= 1.0 else '🔄 进行中' if capability.coverage_score >= 0.5 else '❌ 不足'}

"""
        
        report += """
## 证据条目详情

"""
        
        for evidence in self.evidence_entries.values():
            report += f"""
### {evidence.title}
- **类型**: {evidence.evidence_type.value}
- **来源**: {evidence.source.value}
- **相关性分数**: {evidence.relevance_score:.2f}
- **发布日期**: {evidence.publication_date.strftime('%Y-%m-%d')}
- **DOI**: {evidence.doi or 'N/A'}
- **URL**: {evidence.url or 'N/A'}
- **关键词**: {', '.join(evidence.keywords)}

"""
        
        return report
    
    def save_evidence_data(self, filepath: str = "evidence-data.json"):
        """保存证据数据"""
        data = {
            "evidence_entries": {eid: asdict(entry) for eid, entry in self.evidence_entries.items()},
            "industry_capabilities": {cid: asdict(cap) for cid, cap in self.industry_capabilities.items()},
            "timestamp": datetime.datetime.now().isoformat()
        }
        
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False, default=str)
        
        print(f"证据数据已保存到: {filepath}")


def main():
    """主函数 - 演示证据增强系统"""
    enhancer = EvidenceEnhancer()
    
    print("=== 行业证据实证化增强系统演示 ===")
    
    # 增强行业能力证据
    capabilities = enhancer.enhance_industry_capabilities()
    
    # 生成报告
    report = enhancer.generate_evidence_report()
    print(report)
    
    # 保存数据
    enhancer.save_evidence_data()
    
    # 显示统计信息
    print(f"\n=== 统计信息 ===")
    print(f"总证据条目数: {len(enhancer.evidence_entries)}")
    print(f"行业能力数: {len(enhancer.industry_capabilities)}")
    
    completed_capabilities = sum(1 for c in capabilities.values() if c.coverage_score >= 1.0)
    print(f"完成的能力数: {completed_capabilities}/{len(capabilities)}")
    
    avg_coverage = sum(c.coverage_score for c in capabilities.values()) / len(capabilities)
    print(f"平均覆盖分数: {avg_coverage:.2%}")


if __name__ == "__main__":
    main()
