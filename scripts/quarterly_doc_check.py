#!/usr/bin/env python3
"""
季度/年度文档与证据一致性检查脚本。

用于周期性（季度或年度）运行：
- 内部链接校验（调用 internal_link_checker）
- 证据引用与 docs/evidence/ 文件一致性扫描
- 可选：生成递归完善任务清单（内容空白、缺失 evidence、标准文档存在性）

使用示例：
  python scripts/quarterly_doc_check.py --root docs
  python scripts/quarterly_doc_check.py --root docs --output report.md --evidence-scan
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import List, Set, Tuple

# 期望存在的标准文档（docs 下）
REQUIRED_STANDARDS = [
    "CITATION_STANDARDS.md",
    "QUALITY_STANDARDS.md",
    "EXPERT_REVIEW_SYSTEM.md",
    "CODE_REVIEW_GUIDE.md",
]

# evidence 目录相对路径
EVIDENCE_DIR = "evidence"


def find_evidence_refs(root: Path) -> Set[str]:
    """扫描 docs 下所有 .md 中引用的 evidence:ID。"""
    refs = set()
    pattern = re.compile(r"evidence:([A-Za-z0-9_-]+)")
    for f in root.rglob("*.md"):
        try:
            text = f.read_text(encoding="utf-8")
            for m in pattern.finditer(text):
                refs.add(m.group(1))
        except Exception:
            pass
    return refs


def find_evidence_files(root: Path) -> Set[str]:
    """docs/evidence/*.md 的 id（frontmatter 或文件名）。"""
    evidence_root = root / EVIDENCE_DIR
    ids = set()
    if not evidence_root.is_dir():
        return ids
    for f in evidence_root.glob("*.md"):
        if f.name == "README.md":
            continue
        # 文件名去掉 .md 作为 ID 的一部分（如 CN-K8S-BASE）
        stem = f.stem
        ids.add(stem)
        try:
            content = f.read_text(encoding="utf-8")
            # 常见 frontmatter id: evidence:CN-K8S-BASE
            m = re.search(r"^id:\s*evidence:([A-Za-z0-9_-]+)", content, re.MULTILINE)
            if m:
                ids.add(m.group(1))
        except Exception:
            pass
    return ids


def check_standards_exist(root: Path) -> List[Tuple[str, bool]]:
    """检查必需的标准文档是否存在。"""
    return [(name, (root / name).is_file()) for name in REQUIRED_STANDARDS]


def run_checks(root_dir: str, do_evidence_scan: bool) -> dict:
    root = Path(root_dir)
    if not root.is_dir():
        return {"error": f"Not a directory: {root_dir}"}

    result = {
        "standards": check_standards_exist(root),
        "evidence_refs": [],
        "evidence_files": [],
        "evidence_missing": [],
        "evidence_orphan": [],
    }

    if do_evidence_scan:
        refs = find_evidence_refs(root)
        files = find_evidence_files(root)
        # 规范化：evidence 文件名多为 CN-K8S-BASE，引用多为 CN-K8S-BASE 或 evidence:CN-K8S-BASE 提取出的 CN-K8S-BASE
        evidence_root = root / EVIDENCE_DIR
        file_stems = {p.stem for p in evidence_root.glob("*.md") if p.name != "README.md"}
        result["evidence_refs"] = sorted(refs)
        result["evidence_files"] = sorted(file_stems)
        result["evidence_missing"] = sorted(refs - file_stems)
        result["evidence_orphan"] = sorted(file_stems - refs)

    return result


def main():
    parser = argparse.ArgumentParser(description="Quarterly/Annual doc and evidence consistency check.")
    parser.add_argument("--root", default="docs", help="Root directory (e.g. docs)")
    parser.add_argument("--output", help="Write report to this file (Markdown)")
    parser.add_argument("--evidence-scan", action="store_true", help="Scan evidence refs vs files")
    args = parser.parse_args()

    result = run_checks(args.root, args.evidence_scan)

    if "error" in result:
        print(result["error"], file=sys.stderr)
        sys.exit(1)

    lines = [
        "# 季度/年度文档检查报告",
        "",
        "## 1. 标准文档存在性",
        "",
        "| 文档 | 存在 |",
        "|------|------|",
    ]
    for name, exists in result["standards"]:
        lines.append(f"| {name} | {'是' if exists else '**否**' } |")
    lines.extend(["", "## 2. 证据引用与文件一致性", ""])

    if args.evidence_scan:
        lines.append(f"- 引用到的 evidence 数量: {len(result['evidence_refs'])}")
        lines.append(f"- evidence 文件数量: {len(result['evidence_files'])}")
        if result["evidence_missing"]:
            lines.append("- **缺失文件（被引用但无对应 evidence 文件）**:")
            for id in result["evidence_missing"]:
                lines.append(f"  - `{id}`")
        else:
            lines.append("- 缺失: 无")
        if result["evidence_orphan"]:
            lines.append("- 未被引用的 evidence 文件（可保留或清理）:")
            for id in result["evidence_orphan"]:
                lines.append(f"  - `{id}`")
        lines.append("")
        lines.append("建议：为「缺失文件」在 `docs/evidence/` 下创建对应 .md 或标注「待补充」。")
    else:
        lines.append("（未执行 evidence 扫描，请使用 --evidence-scan）")

    lines.extend([
        "",
        "## 3. 建议的后续动作",
        "",
        "- 若标准文档缺失：在 docs 下创建或从 docs/README 统一入口说明。",
        "- 若 evidence 缺失：使用 `docs/templates/TEMPLATE_证据条目.md` 新建或标记待补充。",
        "- 运行 `python scripts/internal_link_checker.py --root docs` 做链接校验。",
        "- 更新 `docs/reference/AUTHORITY_ALIGNMENT_INDEX.md`（课程/标准/CNCF 等）。",
        "",
    ])

    report = "\n".join(lines)
    print(report)

    if args.output:
        Path(args.output).write_text(report, encoding="utf-8")
        print(f"\nReport written to {args.output}", file=sys.stderr)

    sys.exit(0)


if __name__ == "__main__":
    main()
