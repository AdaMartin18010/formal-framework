#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework 知识图谱生成工具

自动分析项目文档，生成知识图谱和概念关联关系
"""

import os
import yaml
import json
import re
import networkx as nx
import matplotlib.pyplot as plt
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime
import argparse
from collections import defaultdict


@dataclass
class Concept:
    """概念节点"""
    name: str
    type: str
    file_path: str
    description: str
    keywords: List[str]
    relationships: List[str]


@dataclass
class Relationship:
    """关系边"""
    source: str
    target: str
    type: str
    weight: float
    description: str


@dataclass
class KnowledgeGraph:
    """知识图谱"""
    concepts: Dict[str, Concept]
    relationships: List[Relationship]
    graph: nx.DiGraph
    metadata: Dict


class KnowledgeGraphGenerator:
    """知识图谱生成器"""
    
    def __init__(self, config_path: str = "config/automation_config.yaml"):
        """初始化知识图谱生成器"""
        self.config = self._load_config(config_path)
        self.concepts = {}
        self.relationships = []
        
    def _load_config(self, config_path: str) -> Dict:
        """加载配置文件"""
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        except FileNotFoundError:
            print(f"警告: 配置文件 {config_path} 不存在，使用默认配置")
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict:
        """获取默认配置"""
        return {
            'knowledge_graph': {
                'layout': 'spring',
                'node_size': 1000,
                'font_size': 8,
                'output_format': 'png',
                'include_weights': True
            },
            'concept_extraction': {
                'min_concept_length': 2,
                'max_concept_length': 50,
                'stop_words': ['的', '是', '在', '有', '和', '与', '或', '但', '而', '则', '如果', '那么'],
                'concept_patterns': [
                    r'([A-Z][a-z]+(?:\s+[A-Z][a-z]+)*)',  # 驼峰命名
                    r'([A-Z]+(?:_[A-Z]+)*)',  # 下划线命名
                    r'([\u4e00-\u9fa5]+(?:模型|系统|架构|框架|理论|方法|技术|工具|平台|服务|协议|标准|规范|流程|过程|机制|算法|模式|设计|实现|部署|监控|测试|验证|分析|优化|管理|控制|调度|编排|存储|计算|网络|安全|性能|质量|可靠性|可用性|可扩展性|可维护性|可观测性|可追溯性|可验证性|可证明性|可扩展性|可组合性|可重用性|可配置性|可定制性|可插拔性|可替换性|可升级性|可回滚性|可恢复性|可容错性|可一致性|可隔离性|可限流性|可熔断性|可降级性|可监控性|可告警性|可追踪性|可分析性|可优化性|可管理性|可控制性|可调度性|可编排性|可存储性|可计算性|可网络性|可安全性|可性能性|可质量性|可可靠性|可可用性))',
                ]
            },
            'relationship_extraction': {
                'relationship_patterns': [
                    (r'([^。，；！？]+)(包含|包括|由|组成|构成|形成|建立|构建|创建|定义|描述|说明|解释|阐述|介绍|概述|总结|归纳|概括|抽象|具体|实例|示例|案例|应用|使用|实现|部署|监控|测试|验证|分析|优化|管理|控制|调度|编排|存储|计算|网络|安全|性能|质量|可靠性|可用性|可扩展性|可维护性|可观测性|可追溯性|可验证性|可证明性|可扩展性|可组合性|可重用性|可配置性|可定制性|可插拔性|可替换性|可升级性|可回滚性|可恢复性|可容错性|可一致性|可隔离性|可限流性|可熔断性|可降级性|可监控性|可告警性|可追踪性|可分析性|可优化性|可管理性|可控制性|可调度性|可编排性|可存储性|可计算性|可网络性|可安全性|可性能性|可质量性|可可靠性|可可用性)([^。，；！？]+)', '包含'),
                    (r'([^。，；！？]+)(基于|依赖|使用|调用|引用|参考|继承|扩展|实现|遵循|符合|满足|支持|提供|服务|接口|协议|标准|规范|流程|过程|机制|算法|模式|设计|实现|部署|监控|测试|验证|分析|优化|管理|控制|调度|编排|存储|计算|网络|安全|性能|质量|可靠性|可用性|可扩展性|可维护性|可观测性|可追溯性|可验证性|可证明性|可扩展性|可组合性|可重用性|可配置性|可定制性|可插拔性|可替换性|可升级性|可回滚性|可恢复性|可容错性|可一致性|可隔离性|可限流性|可熔断性|可降级性|可监控性|可告警性|可追踪性|可分析性|可优化性|可管理性|可控制性|可调度性|可编排性|可存储性|可计算性|可网络性|可安全性|可性能性|可质量性|可可靠性|可可用性)([^。，；！？]+)', '依赖'),
                    (r'([^。，；！？]+)(与|和|或|但|而|则|如果|那么|当|时|在|中|里|内|外|上|下|左|右|前|后|早|晚|快|慢|高|低|大|小|多|少|好|坏|优|劣|强|弱|新|旧|老|年轻|成熟|稳定|不稳定|可靠|不可靠|可用|不可用|可扩展|不可扩展|可维护|不可维护|可观测|不可观测|可追溯|不可追溯|可验证|不可验证|可证明|不可证明|可扩展|不可扩展|可组合|不可组合|可重用|不可重用|可配置|不可配置|可定制|不可定制|可插拔|不可插拔|可替换|不可替换|可升级|不可升级|可回滚|不可回滚|可恢复|不可恢复|可容错|不可容错|可一致|不可一致|可隔离|不可隔离|可限流|不可限流|可熔断|不可熔断|可降级|不可降级|可监控|不可监控|可告警|不可告警|可追踪|不可追踪|可分析|不可分析|可优化|不可优化|可管理|不可管理|可控制|不可控制|可调度|不可调度|可编排|不可编排|可存储|不可存储|可计算|不可计算|可网络|不可网络|可安全|不可安全|可性能|不可性能|可质量|不可质量|可可靠|不可可靠|可可用|不可可用)([^。，；！？]+)', '关联'),
                ]
            }
        }
    
    def generate_knowledge_graph(self, docs_dir: str = "docs") -> KnowledgeGraph:
        """生成知识图谱"""
        print("开始生成知识图谱...")
        
        # 扫描文档目录
        docs_path = Path(docs_dir)
        if not docs_path.exists():
            print(f"文档目录不存在: {docs_dir}")
            return None
        
        # 提取概念
        self._extract_concepts(docs_path)
        
        # 提取关系
        self._extract_relationships(docs_path)
        
        # 构建图
        graph = self._build_graph()
        
        # 创建知识图谱对象
        knowledge_graph = KnowledgeGraph(
            concepts=self.concepts,
            relationships=self.relationships,
            graph=graph,
            metadata={
                'generation_time': datetime.now().isoformat(),
                'total_concepts': len(self.concepts),
                'total_relationships': len(self.relationships),
                'docs_dir': docs_dir
            }
        )
        
        print(f"知识图谱生成完成: {len(self.concepts)} 个概念, {len(self.relationships)} 个关系")
        return knowledge_graph
    
    def _extract_concepts(self, docs_path: Path):
        """提取概念"""
        print("正在提取概念...")
        
        for file_path in docs_path.rglob("*.md"):
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # 从文件名提取概念
                file_concept = self._extract_file_concept(file_path)
                if file_concept:
                    self.concepts[file_concept] = Concept(
                        name=file_concept,
                        type=self._get_concept_type(file_path),
                        file_path=str(file_path),
                        description=self._extract_description(content),
                        keywords=self._extract_keywords(content),
                        relationships=[]
                    )
                
                # 从内容提取概念
                content_concepts = self._extract_content_concepts(content, file_path)
                for concept_name, concept_info in content_concepts.items():
                    if concept_name not in self.concepts:
                        self.concepts[concept_name] = Concept(
                            name=concept_name,
                            type=concept_info['type'],
                            file_path=str(file_path),
                            description=concept_info['description'],
                            keywords=concept_info['keywords'],
                            relationships=[]
                        )
                    else:
                        # 更新现有概念
                        existing = self.concepts[concept_name]
                        existing.keywords.extend(concept_info['keywords'])
                        existing.keywords = list(set(existing.keywords))  # 去重
                
            except Exception as e:
                print(f"处理文件失败 {file_path}: {e}")
    
    def _extract_file_concept(self, file_path: Path) -> Optional[str]:
        """从文件名提取概念"""
        # 从路径中提取概念名
        path_parts = file_path.parts
        
        # 查找理论或DSL文件
        if 'theory.md' in path_parts or 'dsl-draft.md' in path_parts:
            # 获取父目录名作为概念名
            parent_dir = file_path.parent.name
            if parent_dir and parent_dir not in ['docs', 'formal-model', 'industry-model']:
                return parent_dir.replace('-', ' ')
        
        return None
    
    def _get_concept_type(self, file_path: Path) -> str:
        """获取概念类型"""
        if 'theory.md' in file_path.parts:
            return 'theory'
        elif 'dsl-draft.md' in file_path.parts:
            return 'dsl'
        elif 'formal-model' in file_path.parts:
            return 'formal_model'
        elif 'industry-model' in file_path.parts:
            return 'industry_model'
        else:
            return 'general'
    
    def _extract_description(self, content: str) -> str:
        """提取描述"""
        # 查找第一个段落作为描述
        paragraphs = [p.strip() for p in content.split('\n\n') if p.strip()]
        for paragraph in paragraphs:
            if len(paragraph) > 20 and not paragraph.startswith('#'):
                return paragraph[:200] + '...' if len(paragraph) > 200 else paragraph
        
        return "暂无描述"
    
    def _extract_keywords(self, content: str) -> List[str]:
        """提取关键词"""
        keywords = []
        
        # 从标题中提取关键词
        lines = content.split('\n')
        for line in lines:
            if line.strip().startswith('#'):
                title = line.strip().lstrip('#').strip()
                keywords.extend(self._extract_words_from_text(title))
        
        # 从内容中提取关键词
        keywords.extend(self._extract_words_from_text(content))
        
        # 去重并限制数量
        keywords = list(set(keywords))
        return keywords[:20]  # 最多20个关键词
    
    def _extract_words_from_text(self, text: str) -> List[str]:
        """从文本中提取词汇"""
        words = []
        
        # 使用正则表达式提取词汇
        for pattern in self.config['concept_extraction']['concept_patterns']:
            matches = re.findall(pattern, text)
            for match in matches:
                if isinstance(match, tuple):
                    words.extend(match)
                else:
                    words.append(match)
        
        # 过滤停用词和短词
        stop_words = set(self.config['concept_extraction']['stop_words'])
        min_length = self.config['concept_extraction']['min_concept_length']
        max_length = self.config['concept_extraction']['max_concept_length']
        
        filtered_words = []
        for word in words:
            if (word not in stop_words and 
                min_length <= len(word) <= max_length and
                word.strip()):
                filtered_words.append(word.strip())
        
        return filtered_words
    
    def _extract_content_concepts(self, content: str, file_path: Path) -> Dict[str, Dict]:
        """从内容中提取概念"""
        concepts = {}
        
        # 从标题中提取概念
        lines = content.split('\n')
        for line in lines:
            if line.strip().startswith('#'):
                title = line.strip().lstrip('#').strip()
                if title and len(title) > 2:
                    concepts[title] = {
                        'type': 'section',
                        'description': f"章节: {title}",
                        'keywords': self._extract_words_from_text(title)
                    }
        
        return concepts
    
    def _extract_relationships(self, docs_path: Path):
        """提取关系"""
        print("正在提取关系...")
        
        for file_path in docs_path.rglob("*.md"):
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # 提取文件内的关系
                file_relationships = self._extract_file_relationships(content, file_path)
                self.relationships.extend(file_relationships)
                
                # 提取文件间的关系
                cross_file_relationships = self._extract_cross_file_relationships(content, file_path)
                self.relationships.extend(cross_file_relationships)
                
            except Exception as e:
                print(f"提取关系失败 {file_path}: {e}")
    
    def _extract_file_relationships(self, content: str, file_path: Path) -> List[Relationship]:
        """提取文件内的关系"""
        relationships = []
        
        # 使用关系模式匹配
        for pattern, rel_type in self.config['relationship_extraction']['relationship_patterns']:
            matches = re.findall(pattern, content)
            for match in matches:
                if isinstance(match, tuple) and len(match) >= 2:
                    source, target = match[0], match[2] if len(match) > 2 else match[1]
                    
                    # 检查概念是否存在
                    if source in self.concepts and target in self.concepts:
                        relationship = Relationship(
                            source=source,
                            target=target,
                            type=rel_type,
                            weight=1.0,
                            description=f"{source} {rel_type} {target}"
                        )
                        relationships.append(relationship)
        
        return relationships
    
    def _extract_cross_file_relationships(self, content: str, file_path: Path) -> List[Relationship]:
        """提取文件间的关系"""
        relationships = []
        
        # 查找对其他文件的引用
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        matches = re.findall(link_pattern, content)
        
        for link_text, link_path in matches:
            # 解析链接路径
            if link_path.startswith('./') or link_path.startswith('../'):
                # 相对路径
                target_path = file_path.parent / link_path
                if target_path.exists() and target_path.suffix == '.md':
                    # 查找目标文件对应的概念
                    target_concept = self._extract_file_concept(target_path)
                    source_concept = self._extract_file_concept(file_path)
                    
                    if target_concept and source_concept:
                        relationship = Relationship(
                            source=source_concept,
                            target=target_concept,
                            type='引用',
                            weight=0.5,
                            description=f"{source_concept} 引用 {target_concept}"
                        )
                        relationships.append(relationship)
        
        return relationships
    
    def _build_graph(self) -> nx.DiGraph:
        """构建图"""
        graph = nx.DiGraph()
        
        # 添加节点
        for concept_name, concept in self.concepts.items():
            graph.add_node(concept_name, 
                          type=concept.type,
                          description=concept.description,
                          keywords=concept.keywords,
                          file_path=concept.file_path)
        
        # 添加边
        for relationship in self.relationships:
            if relationship.source in self.concepts and relationship.target in self.concepts:
                graph.add_edge(relationship.source, 
                              relationship.target,
                              type=relationship.type,
                              weight=relationship.weight,
                              description=relationship.description)
        
        return graph
    
    def visualize_graph(self, knowledge_graph: KnowledgeGraph, output_path: str = None):
        """可视化知识图谱"""
        if output_path is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_path = f"reports/knowledge_graph_{timestamp}.png"
        
        graph = knowledge_graph.graph
        
        # 设置图形大小
        plt.figure(figsize=(20, 16))
        
        # 选择布局算法
        layout_config = self.config['knowledge_graph']
        if layout_config['layout'] == 'spring':
            pos = nx.spring_layout(graph, k=3, iterations=50)
        elif layout_config['layout'] == 'circular':
            pos = nx.circular_layout(graph)
        elif layout_config['layout'] == 'random':
            pos = nx.random_layout(graph)
        else:
            pos = nx.spring_layout(graph)
        
        # 绘制节点
        node_colors = []
        node_sizes = []
        
        for node in graph.nodes():
            node_type = graph.nodes[node].get('type', 'general')
            if node_type == 'theory':
                node_colors.append('lightblue')
                node_sizes.append(layout_config['node_size'] * 1.2)
            elif node_type == 'dsl':
                node_colors.append('lightgreen')
                node_sizes.append(layout_config['node_size'] * 1.1)
            elif node_type == 'formal_model':
                node_colors.append('lightcoral')
                node_sizes.append(layout_config['node_size'])
            elif node_type == 'industry_model':
                node_colors.append('lightyellow')
                node_sizes.append(layout_config['node_size'])
            else:
                node_colors.append('lightgray')
                node_sizes.append(layout_config['node_size'] * 0.8)
        
        nx.draw_networkx_nodes(graph, pos, 
                              node_color=node_colors,
                              node_size=node_sizes,
                              alpha=0.8)
        
        # 绘制边
        edge_colors = []
        edge_weights = []
        
        for u, v, data in graph.edges(data=True):
            edge_type = data.get('type', '关联')
            if edge_type == '包含':
                edge_colors.append('red')
                edge_weights.append(2.0)
            elif edge_type == '依赖':
                edge_colors.append('blue')
                edge_weights.append(1.5)
            elif edge_type == '引用':
                edge_colors.append('green')
                edge_weights.append(1.0)
            else:
                edge_colors.append('gray')
                edge_weights.append(0.5)
        
        nx.draw_networkx_edges(graph, pos,
                              edge_color=edge_colors,
                              width=edge_weights,
                              alpha=0.6,
                              arrows=True,
                              arrowsize=20)
        
        # 绘制标签
        nx.draw_networkx_labels(graph, pos,
                               font_size=layout_config['font_size'],
                               font_family='SimHei')
        
        # 添加图例
        legend_elements = [
            plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='lightblue', markersize=10, label='理论'),
            plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='lightgreen', markersize=10, label='DSL'),
            plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='lightcoral', markersize=10, label='形式化模型'),
            plt.Line2D([0], [0], marker='o', color='w', markerfacecolor='lightyellow', markersize=10, label='行业模型'),
            plt.Line2D([0], [0], color='red', label='包含'),
            plt.Line2D([0], [0], color='blue', label='依赖'),
            plt.Line2D([0], [0], color='green', label='引用')
        ]
        
        plt.legend(handles=legend_elements, loc='upper left', bbox_to_anchor=(1, 1))
        
        plt.title('Formal Framework 知识图谱', fontsize=16, fontweight='bold')
        plt.axis('off')
        plt.tight_layout()
        
        # 保存图片
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"知识图谱已保存到: {output_path}")
        return output_path
    
    def export_graph_data(self, knowledge_graph: KnowledgeGraph, output_path: str = None):
        """导出图谱数据"""
        if output_path is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_path = f"reports/knowledge_graph_data_{timestamp}.json"
        
        # 准备导出数据
        export_data = {
            'metadata': knowledge_graph.metadata,
            'concepts': {},
            'relationships': []
        }
        
        # 导出概念
        for concept_name, concept in knowledge_graph.concepts.items():
            export_data['concepts'][concept_name] = {
                'name': concept.name,
                'type': concept.type,
                'file_path': concept.file_path,
                'description': concept.description,
                'keywords': concept.keywords
            }
        
        # 导出关系
        for relationship in knowledge_graph.relationships:
            export_data['relationships'].append({
                'source': relationship.source,
                'target': relationship.target,
                'type': relationship.type,
                'weight': relationship.weight,
                'description': relationship.description
            })
        
        # 保存数据
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(export_data, f, ensure_ascii=False, indent=2)
        
        print(f"图谱数据已导出到: {output_path}")
        return output_path
    
    def generate_graph_report(self, knowledge_graph: KnowledgeGraph, output_path: str = None) -> str:
        """生成图谱报告"""
        if output_path is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_path = f"reports/knowledge_graph_report_{timestamp}.md"
        
        graph = knowledge_graph.graph
        
        report_content = f"""# 知识图谱生成报告

**生成时间**: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

## 图谱概览

- **概念总数**: {len(knowledge_graph.concepts)}
- **关系总数**: {len(knowledge_graph.relationships)}
- **节点类型分布**:
"""
        
        # 统计节点类型
        type_counts = defaultdict(int)
        for concept in knowledge_graph.concepts.values():
            type_counts[concept.type] += 1
        
        for concept_type, count in type_counts.items():
            report_content += f"  - **{concept_type}**: {count} 个\n"
        
        # 统计关系类型
        rel_type_counts = defaultdict(int)
        for relationship in knowledge_graph.relationships:
            rel_type_counts[relationship.type] += 1
        
        report_content += "\n- **关系类型分布**:\n"
        for rel_type, count in rel_type_counts.items():
            report_content += f"  - **{rel_type}**: {count} 个\n"
        
        # 中心性分析
        if len(graph.nodes()) > 0:
            centrality = nx.degree_centrality(graph)
            top_concepts = sorted(centrality.items(), key=lambda x: x[1], reverse=True)[:10]
            
            report_content += "\n## 核心概念 (基于度中心性)\n\n"
            for concept, centrality_score in top_concepts:
                report_content += f"- **{concept}**: {centrality_score:.3f}\n"
        
        # 社区检测
        if len(graph.nodes()) > 1:
            try:
                communities = list(nx.community.greedy_modularity_communities(graph.to_undirected()))
                report_content += f"\n## 社区结构\n\n"
                report_content += f"检测到 {len(communities)} 个社区:\n\n"
                
                for i, community in enumerate(communities, 1):
                    report_content += f"### 社区 {i} ({len(community)} 个概念)\n"
                    for concept in sorted(community):
                        report_content += f"- {concept}\n"
                    report_content += "\n"
            except:
                report_content += "\n## 社区结构\n\n无法进行社区检测\n"
        
        # 概念详情
        report_content += "\n## 概念详情\n\n"
        for concept_name, concept in sorted(knowledge_graph.concepts.items()):
            report_content += f"### {concept_name}\n"
            report_content += f"- **类型**: {concept.type}\n"
            report_content += f"- **文件**: `{concept.file_path}`\n"
            report_content += f"- **描述**: {concept.description}\n"
            report_content += f"- **关键词**: {', '.join(concept.keywords[:10])}\n"
            
            # 相关概念
            neighbors = list(graph.neighbors(concept_name))
            if neighbors:
                report_content += f"- **相关概念**: {', '.join(neighbors[:5])}\n"
            
            report_content += "\n"
        
        # 保存报告
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report_content)
        
        print(f"图谱报告已保存到: {output_path}")
        return output_path


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Formal Framework 知识图谱生成工具')
    parser.add_argument('--config', default='config/automation_config.yaml', help='配置文件路径')
    parser.add_argument('--docs-dir', default='docs', help='文档目录路径')
    parser.add_argument('--output-dir', help='输出目录')
    parser.add_argument('--visualize', action='store_true', help='生成可视化图片')
    parser.add_argument('--export-data', action='store_true', help='导出图谱数据')
    parser.add_argument('--report', action='store_true', help='生成报告')
    
    args = parser.parse_args()
    
    # 创建知识图谱生成器
    generator = KnowledgeGraphGenerator(args.config)
    
    # 生成知识图谱
    knowledge_graph = generator.generate_knowledge_graph(args.docs_dir)
    
    if knowledge_graph:
        output_dir = args.output_dir or "reports"
        
        # 生成可视化
        if args.visualize:
            generator.visualize_graph(knowledge_graph, f"{output_dir}/knowledge_graph.png")
        
        # 导出数据
        if args.export_data:
            generator.export_graph_data(knowledge_graph, f"{output_dir}/knowledge_graph_data.json")
        
        # 生成报告
        if args.report:
            generator.generate_graph_report(knowledge_graph, f"{output_dir}/knowledge_graph_report.md")
        
        print("知识图谱生成完成!")
    else:
        print("知识图谱生成失败!")


if __name__ == "__main__":
    main() 