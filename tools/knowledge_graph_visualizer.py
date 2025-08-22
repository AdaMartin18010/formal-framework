#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework 知识图谱可视化工具

该工具提供知识图谱的可视化展示和交互式探索功能，
支持多种可视化格式和交互方式。

作者: Formal Framework Team
版本: 1.0.0
日期: 2025-02-10
"""

import os
import json
import yaml
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
import logging

try:
    import networkx as nx
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    from matplotlib.patches import FancyBboxPatch
    import numpy as np
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("警告: matplotlib 未安装，将使用文本模式输出")

try:
    import plotly.graph_objects as go
    import plotly.express as px
    from plotly.subplots import make_subplots
    HAS_PLOTLY = True
except ImportError:
    HAS_PLOTLY = False
    print("警告: plotly 未安装，交互式可视化功能不可用")

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


@dataclass
class KnowledgeNode:
    """知识节点数据类"""
    id: str
    name: str
    type: str
    description: Optional[str] = None
    properties: Optional[Dict] = None
    position: Optional[Tuple[float, float]] = None


@dataclass
class KnowledgeRelation:
    """知识关系数据类"""
    source: str
    target: str
    type: str
    description: Optional[str] = None
    weight: Optional[float] = None


@dataclass
class KnowledgeGraph:
    """知识图谱数据类"""
    nodes: List[KnowledgeNode]
    relations: List[KnowledgeRelation]
    metadata: Optional[Dict] = None


class KnowledgeGraphParser:
    """知识图谱解析器"""
    
    def __init__(self):
        self.supported_formats = ['.json', '.yaml', '.yml', '.md']
    
    def parse_file(self, file_path: str) -> KnowledgeGraph:
        """解析知识图谱文件"""
        file_path = Path(file_path)
        
        if not file_path.exists():
            raise FileNotFoundError(f"文件不存在: {file_path}")
        
        if file_path.suffix.lower() not in self.supported_formats:
            raise ValueError(f"不支持的文件格式: {file_path.suffix}")
        
        if file_path.suffix.lower() in ['.yaml', '.yml']:
            return self._parse_yaml(file_path)
        elif file_path.suffix.lower() == '.json':
            return self._parse_json(file_path)
        elif file_path.suffix.lower() == '.md':
            return self._parse_markdown(file_path)
        else:
            raise ValueError(f"不支持的文件格式: {file_path.suffix}")
    
    def _parse_yaml(self, file_path: Path) -> KnowledgeGraph:
        """解析YAML格式的知识图谱"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
            
            return self._build_knowledge_graph(data)
        except Exception as e:
            logger.error(f"解析YAML文件失败: {e}")
            raise
    
    def _parse_json(self, file_path: Path) -> KnowledgeGraph:
        """解析JSON格式的知识图谱"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            return self._build_knowledge_graph(data)
        except Exception as e:
            logger.error(f"解析JSON文件失败: {e}")
            raise
    
    def _parse_markdown(self, file_path: Path) -> KnowledgeGraph:
        """解析Markdown格式的知识图谱"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 提取YAML代码块
            import re
            yaml_pattern = r'```yaml\s*\n(.*?)\n```'
            yaml_matches = re.findall(yaml_pattern, content, re.DOTALL)
            
            if yaml_matches:
                data = yaml.safe_load(yaml_matches[0])
                return self._build_knowledge_graph(data)
            else:
                raise ValueError("未找到YAML代码块")
        except Exception as e:
            logger.error(f"解析Markdown文件失败: {e}")
            raise
    
    def _build_knowledge_graph(self, data: Dict) -> KnowledgeGraph:
        """构建知识图谱对象"""
        nodes = []
        relations = []
        
        # 解析节点
        if 'entities' in data:
            for entity in data['entities']:
                node = KnowledgeNode(
                    id=entity.get('id', ''),
                    name=entity.get('name', ''),
                    type=entity.get('type', 'unknown'),
                    description=entity.get('description'),
                    properties=entity.get('properties')
                )
                nodes.append(node)
        
        if 'concepts' in data:
            for concept in data['concepts']:
                node = KnowledgeNode(
                    id=concept.get('id', ''),
                    name=concept.get('name', ''),
                    type=concept.get('type', 'concept'),
                    description=concept.get('description'),
                    properties=concept.get('properties')
                )
                nodes.append(node)
        
        # 解析关系
        if 'relationships' in data:
            for rel in data['relationships']:
                relation = KnowledgeRelation(
                    source=rel.get('source', ''),
                    target=rel.get('target', ''),
                    type=rel.get('type', ''),
                    description=rel.get('description'),
                    weight=rel.get('weight', 1.0)
                )
                relations.append(relation)
        
        return KnowledgeGraph(
            nodes=nodes,
            relations=relations,
            metadata=data.get('metadata')
        )


class NetworkXVisualizer:
    """基于NetworkX的可视化器"""
    
    def __init__(self, graph: KnowledgeGraph):
        self.graph = graph
        self.nx_graph = self._build_networkx_graph()
        self.node_colors = self._get_node_colors()
        self.edge_colors = self._get_edge_colors()
    
    def _build_networkx_graph(self) -> nx.DiGraph:
        """构建NetworkX图"""
        G = nx.DiGraph()
        
        # 添加节点
        for node in self.graph.nodes:
            G.add_node(node.id, **asdict(node))
        
        # 添加边
        for relation in self.graph.relations:
            G.add_edge(
                relation.source, 
                relation.target, 
                **asdict(relation)
            )
        
        return G
    
    def _get_node_colors(self) -> List[str]:
        """获取节点颜色"""
        colors = []
        color_map = {
            'core-concept': '#FF6B6B',
            'quality-system': '#4ECDC4',
            'theory-system': '#45B7D1',
            'concept': '#96CEB4',
            'formal-model': '#FFEAA7',
            'industry-model': '#DDA0DD',
            'quality-principle': '#98D8C8',
            'improvement-method': '#F7DC6F',
            'data-model-innovation': '#BB8FCE',
            'functional-model-innovation': '#85C1E9',
            'industry-architecture': '#F8C471'
        }
        
        for node in self.graph.nodes:
            colors.append(color_map.get(node.type, '#CCCCCC'))
        
        return colors
    
    def _get_edge_colors(self) -> List[str]:
        """获取边颜色"""
        colors = []
        color_map = {
            'depends_on': '#E74C3C',
            'supports': '#27AE60',
            'maps_to': '#3498DB',
            'contains': '#F39C12',
            'relates_to': '#9B59B6'
        }
        
        for relation in self.graph.relations:
            colors.append(color_map.get(relation.type, '#95A5A6'))
        
        return colors
    
    def visualize(self, output_path: Optional[str] = None, 
                  layout: str = 'spring', figsize: Tuple[int, int] = (12, 8)):
        """可视化知识图谱"""
        if not HAS_MATPLOTLIB:
            logger.error("matplotlib 未安装，无法进行可视化")
            return
        
        plt.figure(figsize=figsize)
        
        # 选择布局算法
        if layout == 'spring':
            pos = nx.spring_layout(self.nx_graph, k=1, iterations=50)
        elif layout == 'circular':
            pos = nx.circular_layout(self.nx_graph)
        elif layout == 'random':
            pos = nx.random_layout(self.nx_graph)
        elif layout == 'shell':
            pos = nx.shell_layout(self.nx_graph)
        else:
            pos = nx.spring_layout(self.nx_graph)
        
        # 绘制节点
        nx.draw_networkx_nodes(
            self.nx_graph, pos,
            node_color=self.node_colors,
            node_size=1000,
            alpha=0.8
        )
        
        # 绘制边
        nx.draw_networkx_edges(
            self.nx_graph, pos,
            edge_color=self.edge_colors,
            arrows=True,
            arrowsize=20,
            alpha=0.6
        )
        
        # 绘制标签
        labels = {node.id: node.name for node in self.graph.nodes}
        nx.draw_networkx_labels(
            self.nx_graph, pos, labels,
            font_size=8,
            font_family='SimHei'
        )
        
        # 添加图例
        self._add_legend()
        
        plt.title("Formal Framework 知识图谱", fontsize=16, fontweight='bold')
        plt.axis('off')
        
        if output_path:
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            logger.info(f"图像已保存到: {output_path}")
        else:
            plt.show()
        
        plt.close()
    
    def _add_legend(self):
        """添加图例"""
        node_types = set(node.type for node in self.graph.nodes)
        color_map = {
            'core-concept': '#FF6B6B',
            'quality-system': '#4ECDC4',
            'theory-system': '#45B7D1',
            'concept': '#96CEB4',
            'formal-model': '#FFEAA7',
            'industry-model': '#DDA0DD',
            'quality-principle': '#98D8C8',
            'improvement-method': '#F7DC6F',
            'data-model-innovation': '#BB8FCE',
            'functional-model-innovation': '#85C1E9',
            'industry-architecture': '#F8C471'
        }
        
        legend_elements = []
        for node_type in sorted(node_types):
            color = color_map.get(node_type, '#CCCCCC')
            legend_elements.append(
                mpatches.Patch(color=color, label=node_type.replace('-', ' ').title())
            )
        
        plt.legend(handles=legend_elements, loc='upper left', bbox_to_anchor=(1, 1))


class PlotlyVisualizer:
    """基于Plotly的交互式可视化器"""
    
    def __init__(self, graph: KnowledgeGraph):
        self.graph = graph
        self.node_colors = self._get_node_colors()
        self.edge_colors = self._get_edge_colors()
    
    def _get_node_colors(self) -> List[str]:
        """获取节点颜色"""
        color_map = {
            'core-concept': '#FF6B6B',
            'quality-system': '#4ECDC4',
            'theory-system': '#45B7D1',
            'concept': '#96CEB4',
            'formal-model': '#FFEAA7',
            'industry-model': '#DDA0DD',
            'quality-principle': '#98D8C8',
            'improvement-method': '#F7DC6F',
            'data-model-innovation': '#BB8FCE',
            'functional-model-innovation': '#85C1E9',
            'industry-architecture': '#F8C471'
        }
        
        return [color_map.get(node.type, '#CCCCCC') for node in self.graph.nodes]
    
    def _get_edge_colors(self) -> List[str]:
        """获取边颜色"""
        color_map = {
            'depends_on': '#E74C3C',
            'supports': '#27AE60',
            'maps_to': '#3498DB',
            'contains': '#F39C12',
            'relates_to': '#9B59B6'
        }
        
        return [color_map.get(relation.type, '#95A5A6') for relation in self.graph.relations]
    
    def visualize(self, output_path: Optional[str] = None):
        """交互式可视化知识图谱"""
        if not HAS_PLOTLY:
            logger.error("plotly 未安装，无法进行交互式可视化")
            return
        
        # 创建节点轨迹
        node_trace = go.Scatter(
            x=[],
            y=[],
            text=[],
            mode='markers+text',
            hoverinfo='text',
            marker=dict(
                size=20,
                color=self.node_colors,
                line=dict(width=2, color='white')
            ),
            textposition="middle center",
            textfont=dict(size=10)
        )
        
        # 创建边轨迹
        edge_trace = go.Scatter(
            x=[],
            y=[],
            line=dict(width=1, color=self.edge_colors),
            hoverinfo='none',
            mode='lines'
        )
        
        # 计算布局
        G = nx.DiGraph()
        for node in self.graph.nodes:
            G.add_node(node.id)
        for relation in self.graph.relations:
            G.add_edge(relation.source, relation.target)
        
        pos = nx.spring_layout(G, k=1, iterations=50)
        
        # 添加节点位置
        for node in self.graph.nodes:
            x, y = pos[node.id]
            node_trace['x'] += tuple([x])
            node_trace['y'] += tuple([y])
            node_trace['text'] += tuple([node.name])
        
        # 添加边位置
        for relation in self.graph.relations:
            x0, y0 = pos[relation.source]
            x1, y1 = pos[relation.target]
            edge_trace['x'] += tuple([x0, x1, None])
            edge_trace['y'] += tuple([y0, y1, None])
        
        # 创建图形
        fig = go.Figure(data=[edge_trace, node_trace],
                       layout=go.Layout(
                           title='Formal Framework 知识图谱',
                           showlegend=False,
                           hovermode='closest',
                           margin=dict(b=20, l=5, r=5, t=40),
                           xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
                           yaxis=dict(showgrid=False, zeroline=False, showticklabels=False)
                       ))
        
        if output_path:
            fig.write_html(output_path)
            logger.info(f"交互式图像已保存到: {output_path}")
        else:
            fig.show()


class TextVisualizer:
    """文本模式可视化器"""
    
    def __init__(self, graph: KnowledgeGraph):
        self.graph = graph
    
    def visualize(self, output_path: Optional[str] = None):
        """文本模式可视化"""
        output = []
        output.append("=" * 60)
        output.append("Formal Framework 知识图谱")
        output.append("=" * 60)
        output.append("")
        
        # 节点信息
        output.append("节点信息:")
        output.append("-" * 30)
        for node in self.graph.nodes:
            output.append(f"ID: {node.id}")
            output.append(f"名称: {node.name}")
            output.append(f"类型: {node.type}")
            if node.description:
                output.append(f"描述: {node.description}")
            output.append("")
        
        # 关系信息
        output.append("关系信息:")
        output.append("-" * 30)
        for relation in self.graph.relations:
            output.append(f"源节点: {relation.source}")
            output.append(f"目标节点: {relation.target}")
            output.append(f"关系类型: {relation.type}")
            if relation.description:
                output.append(f"描述: {relation.description}")
            output.append("")
        
        # 统计信息
        output.append("统计信息:")
        output.append("-" * 30)
        output.append(f"节点总数: {len(self.graph.nodes)}")
        output.append(f"关系总数: {len(self.graph.relations)}")
        
        node_types = {}
        for node in self.graph.nodes:
            node_types[node.type] = node_types.get(node.type, 0) + 1
        
        output.append("节点类型分布:")
        for node_type, count in sorted(node_types.items()):
            output.append(f"  {node_type}: {count}")
        
        relation_types = {}
        for relation in self.graph.relations:
            relation_types[relation.type] = relation_types.get(relation.type, 0) + 1
        
        output.append("关系类型分布:")
        for relation_type, count in sorted(relation_types.items()):
            output.append(f"  {relation_type}: {count}")
        
        result = "\n".join(output)
        
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(result)
            logger.info(f"文本报告已保存到: {output_path}")
        else:
            print(result)


class KnowledgeGraphVisualizer:
    """知识图谱可视化主类"""
    
    def __init__(self, graph: KnowledgeGraph):
        self.graph = graph
        self.visualizers = {
            'networkx': NetworkXVisualizer(graph) if HAS_MATPLOTLIB else None,
            'plotly': PlotlyVisualizer(graph) if HAS_PLOTLY else None,
            'text': TextVisualizer(graph)
        }
    
    def visualize(self, method: str = 'networkx', output_path: Optional[str] = None, **kwargs):
        """可视化知识图谱"""
        if method not in self.visualizers:
            raise ValueError(f"不支持的可视化方法: {method}")
        
        visualizer = self.visualizers[method]
        if visualizer is None:
            logger.warning(f"可视化方法 {method} 不可用，使用文本模式")
            visualizer = self.visualizers['text']
        
        visualizer.visualize(output_path, **kwargs)
    
    def export_graph_data(self, output_path: str, format: str = 'json'):
        """导出图数据"""
        if format == 'json':
            data = {
                'nodes': [asdict(node) for node in self.graph.nodes],
                'relations': [asdict(relation) for relation in self.graph.relations],
                'metadata': self.graph.metadata
            }
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        elif format == 'yaml':
            data = {
                'nodes': [asdict(node) for node in self.graph.nodes],
                'relations': [asdict(relation) for relation in self.graph.relations],
                'metadata': self.graph.metadata
            }
            with open(output_path, 'w', encoding='utf-8') as f:
                yaml.dump(data, f, default_flow_style=False, allow_unicode=True)
        else:
            raise ValueError(f"不支持的导出格式: {format}")
        
        logger.info(f"图数据已导出到: {output_path}")


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description="Formal Framework 知识图谱可视化工具")
    parser.add_argument("input", help="输入的知识图谱文件路径")
    parser.add_argument("--method", "-m", default="networkx", 
                       choices=["networkx", "plotly", "text"],
                       help="可视化方法")
    parser.add_argument("--output", "-o", help="输出文件路径")
    parser.add_argument("--format", "-f", default="png",
                       choices=["png", "svg", "pdf", "html", "txt"],
                       help="输出格式")
    parser.add_argument("--layout", "-l", default="spring",
                       choices=["spring", "circular", "random", "shell"],
                       help="布局算法（仅适用于networkx）")
    parser.add_argument("--export", "-e", help="导出图数据文件路径")
    parser.add_argument("--export-format", default="json",
                       choices=["json", "yaml"],
                       help="导出格式")
    
    args = parser.parse_args()
    
    try:
        # 解析知识图谱
        parser = KnowledgeGraphParser()
        graph = parser.parse_file(args.input)
        
        # 创建可视化器
        visualizer = KnowledgeGraphVisualizer(graph)
        
        # 确定输出路径
        if args.output:
            output_path = args.output
        else:
            base_name = Path(args.input).stem
            if args.method == "plotly" or args.format == "html":
                output_path = f"{base_name}_graph.html"
            elif args.method == "text" or args.format == "txt":
                output_path = f"{base_name}_graph.txt"
            else:
                output_path = f"{base_name}_graph.{args.format}"
        
        # 执行可视化
        visualizer.visualize(
            method=args.method,
            output_path=output_path,
            layout=args.layout
        )
        
        # 导出图数据
        if args.export:
            visualizer.export_graph_data(args.export, args.export_format)
        
        logger.info("可视化完成")
        
    except Exception as e:
        logger.error(f"可视化失败: {e}")
        return 1
    
    return 0


if __name__ == "__main__":
    exit(main())
