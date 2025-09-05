#!/bin/bash

# 正式验证框架实施验证脚本
# 用于验证新文档结构的实施结果

set -e

echo "=== 正式验证框架实施验证 ==="
echo "开始时间: $(date)"
echo ""

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 统计变量
TOTAL_CHECKS=0
PASSED_CHECKS=0
FAILED_CHECKS=0
WARNING_CHECKS=0

# 检查函数
check_file_exists() {
    local file_path="$1"
    local description="$2"
    
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    
    if [ -f "$file_path" ]; then
        echo -e "${GREEN}✅ PASS${NC}: $description - $file_path"
        PASSED_CHECKS=$((PASSED_CHECKS + 1))
        return 0
    else
        echo -e "${RED}❌ FAIL${NC}: $description - $file_path"
        FAILED_CHECKS=$((FAILED_CHECKS + 1))
        return 1
    fi
}

check_directory_exists() {
    local dir_path="$1"
    local description="$2"
    
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    
    if [ -d "$dir_path" ]; then
        echo -e "${GREEN}✅ PASS${NC}: $description - $dir_path"
        PASSED_CHECKS=$((PASSED_CHECKS + 1))
        return 0
    else
        echo -e "${RED}❌ FAIL${NC}: $description - $dir_path"
        FAILED_CHECKS=$((FAILED_CHECKS + 1))
        return 1
    fi
}

check_file_content() {
    local file_path="$1"
    local search_text="$2"
    local description="$3"
    
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    
    if [ -f "$file_path" ] && grep -q "$search_text" "$file_path"; then
        echo -e "${GREEN}✅ PASS${NC}: $description - $file_path"
        PASSED_CHECKS=$((PASSED_CHECKS + 1))
        return 0
    else
        echo -e "${RED}❌ FAIL${NC}: $description - $file_path"
        FAILED_CHECKS=$((FAILED_CHECKS + 1))
        return 1
    fi
}

check_file_size() {
    local file_path="$1"
    local min_size="$2"
    local description="$3"
    
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    
    if [ -f "$file_path" ]; then
        local file_size=$(wc -c < "$file_path")
        if [ "$file_size" -ge "$min_size" ]; then
            echo -e "${GREEN}✅ PASS${NC}: $description - $file_path (${file_size} bytes)"
            PASSED_CHECKS=$((PASSED_CHECKS + 1))
            return 0
        else
            echo -e "${YELLOW}⚠️  WARN${NC}: $description - $file_path (${file_size} bytes, expected >= ${min_size})"
            WARNING_CHECKS=$((WARNING_CHECKS + 1))
            return 1
        fi
    else
        echo -e "${RED}❌ FAIL${NC}: $description - $file_path"
        FAILED_CHECKS=$((FAILED_CHECKS + 1))
        return 1
    fi
}

# 开始验证
echo -e "${BLUE}📋 1. 检查核心文档结构${NC}"
echo ""

# 检查主要目录
check_directory_exists "getting-started" "快速开始目录"
check_directory_exists "theory" "理论基础目录"
check_directory_exists "models" "模型定义目录"
check_directory_exists "examples" "实践案例目录"
check_directory_exists "tools" "工具链目录"
check_directory_exists "standards" "标准对比目录"
check_directory_exists "community" "社区资源目录"
check_directory_exists "templates" "文档模板目录"
check_directory_exists "glossary" "术语表目录"
check_directory_exists "archive" "归档文档目录"

echo ""
echo -e "${BLUE}📋 2. 检查核心文档文件${NC}"
echo ""

# 检查主要README文件
check_file_exists "getting-started/README.md" "快速开始README"
check_file_exists "theory/README.md" "理论基础README"
check_file_exists "models/README.md" "模型定义README"
check_file_exists "examples/README.md" "实践案例README"
check_file_exists "tools/README.md" "工具链README"
check_file_exists "standards/README.md" "标准对比README"
check_file_exists "community/README.md" "社区资源README"
check_file_exists "templates/README.md" "文档模板README"
check_file_exists "glossary/README.md" "术语表README"

echo ""
echo -e "${BLUE}📋 3. 检查子目录结构${NC}"
echo ""

# 检查子目录
check_directory_exists "models/meta-models" "元模型目录"
check_directory_exists "models/standard-models" "标准模型目录"
check_directory_exists "models/industry-models" "行业模型目录"
check_directory_exists "examples/cloud-native" "云原生案例目录"
check_directory_exists "examples/finance" "金融案例目录"
check_directory_exists "examples/ai-infrastructure" "AI基础设施案例目录"
check_directory_exists "examples/iot" "IoT案例目录"
check_directory_exists "examples/web3" "Web3案例目录"
check_directory_exists "tools/verification-scripts" "验证脚本目录"
check_directory_exists "tools/testing-frameworks" "测试框架目录"
check_directory_exists "tools/monitoring" "监控工具目录"
check_directory_exists "tools/deployment" "部署工具目录"
check_directory_exists "standards/international" "国际标准目录"
check_directory_exists "standards/industry" "行业标准目录"
check_directory_exists "standards/comparison" "对比分析目录"
check_directory_exists "community/resources" "社区资源目录"
check_directory_exists "archive/legacy" "历史版本目录"
check_directory_exists "archive/deprecated" "废弃内容目录"

echo ""
echo -e "${BLUE}📋 4. 检查重要文档文件${NC}"
echo ""

# 检查重要文档
check_file_exists "NAVIGATION.md" "导航文档"
check_file_exists "IMPROVEMENT_PLAN.md" "改进计划"
check_file_exists "NEW_STRUCTURE_DESIGN.md" "新结构设计"
check_file_exists "TERMINOLOGY_STANDARD.md" "术语标准"
check_file_exists "THEORY_PRACTICE_BRIDGE.md" "理论实践桥梁"
check_file_exists "INTERNATIONAL_STANDARDS_COMPARISON.md" "国际标准对比"
check_file_exists "TOOLCHAIN_ENHANCEMENT.md" "工具链完善"
check_file_exists "VERIFICATION_MATRIX.md" "验证矩阵"
check_file_exists "COMMUNITY_GUIDELINES.md" "社区指南"
check_file_exists "COMMERCIAL_SUPPORT.md" "商业化支持"
check_file_exists "INTERNATIONAL_INFLUENCE.md" "国际影响力"
check_file_exists "IMPLEMENTATION_SUMMARY.md" "实施总结"

echo ""
echo -e "${BLUE}📋 5. 检查模板文件${NC}"
echo ""

# 检查模板文件
check_file_exists "templates/model-template.md" "模型文档模板"
check_file_exists "templates/example-template.md" "案例文档模板"

echo ""
echo -e "${BLUE}📋 6. 检查术语表文件${NC}"
echo ""

# 检查术语表文件
check_file_exists "glossary/chinese.md" "中文术语表"
check_file_exists "glossary/english.md" "英文术语表"

echo ""
echo -e "${BLUE}📋 7. 检查社区文件${NC}"
echo ""

# 检查社区文件
check_file_exists "community/contributing.md" "贡献指南"
check_file_exists "community/code-of-conduct.md" "行为准则"
check_file_exists "community/governance.md" "治理结构"
check_file_exists "community/roadmap.md" "路线图"

echo ""
echo -e "${BLUE}📋 8. 检查标准文件${NC}"
echo ""

# 检查标准文件
check_file_exists "standards/international/README.md" "国际标准README"
check_file_exists "standards/industry/README.md" "行业标准README"

echo ""
echo -e "${BLUE}📋 9. 检查工具文件${NC}"
echo ""

# 检查工具文件
check_file_exists "tools/verification-scripts/README.md" "验证脚本README"
check_file_exists "tools/testing-frameworks/README.md" "测试框架README"

echo ""
echo -e "${BLUE}📋 10. 检查文档内容质量${NC}"
echo ""

# 检查文档内容质量
check_file_size "IMPROVEMENT_PLAN.md" 1000 "改进计划文档大小"
check_file_size "NEW_STRUCTURE_DESIGN.md" 1000 "新结构设计文档大小"
check_file_size "TERMINOLOGY_STANDARD.md" 1000 "术语标准文档大小"
check_file_size "THEORY_PRACTICE_BRIDGE.md" 1000 "理论实践桥梁文档大小"
check_file_size "INTERNATIONAL_STANDARDS_COMPARISON.md" 1000 "国际标准对比文档大小"
check_file_size "TOOLCHAIN_ENHANCEMENT.md" 1000 "工具链完善文档大小"
check_file_size "VERIFICATION_MATRIX.md" 1000 "验证矩阵文档大小"
check_file_size "COMMUNITY_GUIDELINES.md" 1000 "社区指南文档大小"
check_file_size "COMMERCIAL_SUPPORT.md" 1000 "商业化支持文档大小"
check_file_size "INTERNATIONAL_INFLUENCE.md" 1000 "国际影响力文档大小"
check_file_size "IMPLEMENTATION_SUMMARY.md" 1000 "实施总结文档大小"

echo ""
echo -e "${BLUE}📋 11. 检查文档内容完整性${NC}"
echo ""

# 检查文档内容完整性
check_file_content "IMPROVEMENT_PLAN.md" "改进目标" "改进计划包含目标"
check_file_content "NEW_STRUCTURE_DESIGN.md" "目标结构" "新结构设计包含目标结构"
check_file_content "TERMINOLOGY_STANDARD.md" "核心术语表" "术语标准包含核心术语表"
check_file_content "THEORY_PRACTICE_BRIDGE.md" "理论层" "理论实践桥梁包含理论层"
check_file_content "INTERNATIONAL_STANDARDS_COMPARISON.md" "IEEE标准" "国际标准对比包含IEEE标准"
check_file_content "TOOLCHAIN_ENHANCEMENT.md" "Docker化" "工具链完善包含Docker化"
check_file_content "VERIFICATION_MATRIX.md" "验证矩阵" "验证矩阵包含验证矩阵"
check_file_content "COMMUNITY_GUIDELINES.md" "贡献指南" "社区指南包含贡献指南"
check_file_content "COMMERCIAL_SUPPORT.md" "可视化工具" "商业化支持包含可视化工具"
check_file_content "INTERNATIONAL_INFLUENCE.md" "学术发表" "国际影响力包含学术发表"
check_file_content "IMPLEMENTATION_SUMMARY.md" "实施成果" "实施总结包含实施成果"

echo ""
echo -e "${BLUE}📋 12. 检查导航系统${NC}"
echo ""

# 检查导航系统
check_file_content "NAVIGATION.md" "快速开始" "导航包含快速开始"
check_file_content "NAVIGATION.md" "理论基础" "导航包含理论基础"
check_file_content "NAVIGATION.md" "模型定义" "导航包含模型定义"
check_file_content "NAVIGATION.md" "实践案例" "导航包含实践案例"
check_file_content "NAVIGATION.md" "工具链" "导航包含工具链"
check_file_content "NAVIGATION.md" "标准对比" "导航包含标准对比"
check_file_content "NAVIGATION.md" "社区资源" "导航包含社区资源"

echo ""
echo -e "${BLUE}📋 13. 检查链接完整性${NC}"
echo ""

# 检查链接完整性（简化检查）
check_file_content "getting-started/README.md" "installation.md" "快速开始包含安装指南链接"
check_file_content "theory/README.md" "mathematical-foundation.md" "理论基础包含数学基础链接"
check_file_content "models/README.md" "meta-models" "模型定义包含元模型链接"
check_file_content "examples/README.md" "cloud-native" "实践案例包含云原生链接"
check_file_content "tools/README.md" "verification-scripts" "工具链包含验证脚本链接"
check_file_content "standards/README.md" "international" "标准对比包含国际标准链接"
check_file_content "community/README.md" "contributing.md" "社区资源包含贡献指南链接"

echo ""
echo -e "${BLUE}📋 14. 检查术语一致性${NC}"
echo ""

# 检查术语一致性
check_file_content "glossary/chinese.md" "抽象" "中文术语表包含抽象"
check_file_content "glossary/english.md" "Abstraction" "英文术语表包含Abstraction"
check_file_content "TERMINOLOGY_STANDARD.md" "一致性" "术语标准包含一致性"
check_file_content "TERMINOLOGY_STANDARD.md" "准确性" "术语标准包含准确性"
check_file_content "TERMINOLOGY_STANDARD.md" "国际化" "术语标准包含国际化"

echo ""
echo -e "${BLUE}📋 15. 检查模板系统${NC}"
echo ""

# 检查模板系统
check_file_content "templates/model-template.md" "模型名称" "模型模板包含模型名称"
check_file_content "templates/example-template.md" "案例名称" "案例模板包含案例名称"
check_file_content "templates/README.md" "模板列表" "模板README包含模板列表"

echo ""
echo -e "${BLUE}📋 16. 检查社区系统${NC}"
echo ""

# 检查社区系统
check_file_content "community/contributing.md" "贡献方式" "贡献指南包含贡献方式"
check_file_content "community/code-of-conduct.md" "行为标准" "行为准则包含行为标准"
check_file_content "community/governance.md" "治理架构" "治理结构包含治理架构"
check_file_content "community/roadmap.md" "发展愿景" "路线图包含发展愿景"

echo ""
echo -e "${BLUE}📋 17. 检查标准系统${NC}"
echo ""

# 检查标准系统
check_file_content "standards/international/README.md" "IEEE标准" "国际标准包含IEEE标准"
check_file_content "standards/industry/README.md" "金融行业" "行业标准包含金融行业"
check_file_content "standards/README.md" "标准分类" "标准概览包含标准分类"

echo ""
echo -e "${BLUE}📋 18. 检查工具系统${NC}"
echo ""

# 检查工具系统
check_file_content "tools/verification-scripts/README.md" "验证脚本" "验证脚本README包含验证脚本"
check_file_content "tools/testing-frameworks/README.md" "测试框架" "测试框架README包含测试框架"
check_file_content "tools/README.md" "工具分类" "工具概览包含工具分类"

echo ""
echo -e "${BLUE}📋 19. 检查实施完整性${NC}"
echo ""

# 检查实施完整性
check_file_content "IMPLEMENTATION_SUMMARY.md" "实施成果" "实施总结包含实施成果"
check_file_content "IMPLEMENTATION_SUMMARY.md" "关键成就" "实施总结包含关键成就"
check_file_content "IMPLEMENTATION_SUMMARY.md" "量化成果" "实施总结包含量化成果"
check_file_content "IMPLEMENTATION_SUMMARY.md" "下一步行动" "实施总结包含下一步行动"

echo ""
echo -e "${BLUE}📋 20. 检查文档更新状态${NC}"
echo ""

# 检查文档更新状态
check_file_content "IMPROVEMENT_PLAN.md" "2024-12-19" "改进计划包含更新日期"
check_file_content "NEW_STRUCTURE_DESIGN.md" "2024-12-19" "新结构设计包含更新日期"
check_file_content "TERMINOLOGY_STANDARD.md" "2024-12-19" "术语标准包含更新日期"
check_file_content "THEORY_PRACTICE_BRIDGE.md" "2024-12-19" "理论实践桥梁包含更新日期"
check_file_content "INTERNATIONAL_STANDARDS_COMPARISON.md" "2024-12-19" "国际标准对比包含更新日期"
check_file_content "TOOLCHAIN_ENHANCEMENT.md" "2024-12-19" "工具链完善包含更新日期"
check_file_content "VERIFICATION_MATRIX.md" "2024-12-19" "验证矩阵包含更新日期"
check_file_content "COMMUNITY_GUIDELINES.md" "2024-12-19" "社区指南包含更新日期"
check_file_content "COMMERCIAL_SUPPORT.md" "2024-12-19" "商业化支持包含更新日期"
check_file_content "INTERNATIONAL_INFLUENCE.md" "2024-12-19" "国际影响力包含更新日期"
check_file_content "IMPLEMENTATION_SUMMARY.md" "2024-12-19" "实施总结包含更新日期"

echo ""
echo -e "${BLUE}📊 验证结果统计${NC}"
echo ""

# 计算通过率
PASS_RATE=$((PASSED_CHECKS * 100 / TOTAL_CHECKS))
WARNING_RATE=$((WARNING_CHECKS * 100 / TOTAL_CHECKS))
FAIL_RATE=$((FAILED_CHECKS * 100 / TOTAL_CHECKS))

echo -e "${GREEN}✅ 通过检查: ${PASSED_CHECKS}/${TOTAL_CHECKS} (${PASS_RATE}%)${NC}"
echo -e "${YELLOW}⚠️  警告检查: ${WARNING_CHECKS}/${TOTAL_CHECKS} (${WARNING_RATE}%)${NC}"
echo -e "${RED}❌ 失败检查: ${FAILED_CHECKS}/${TOTAL_CHECKS} (${FAIL_RATE}%)${NC}"

echo ""
echo -e "${BLUE}📋 验证总结${NC}"
echo ""

if [ $FAILED_CHECKS -eq 0 ]; then
    if [ $WARNING_CHECKS -eq 0 ]; then
        echo -e "${GREEN}🎉 所有检查都通过了！实施完全成功！${NC}"
        echo -e "${GREEN}✨ 正式验证框架的新文档结构已经完美实施！${NC}"
    else
        echo -e "${GREEN}✅ 所有关键检查都通过了！${NC}"
        echo -e "${YELLOW}⚠️  有一些警告，但不影响整体实施效果。${NC}"
    fi
else
    echo -e "${RED}❌ 有一些检查失败了，需要修复。${NC}"
    echo -e "${YELLOW}⚠️  请检查失败的检查项并修复相关问题。${NC}"
fi

echo ""
echo -e "${BLUE}📋 建议的后续行动${NC}"
echo ""

if [ $FAILED_CHECKS -eq 0 ]; then
    echo -e "${GREEN}1. 开始使用新的文档结构${NC}"
    echo -e "${GREEN}2. 培训团队成员使用新结构${NC}"
    echo -e "${GREEN}3. 开始迁移现有文档${NC}"
    echo -e "${GREEN}4. 建立持续改进机制${NC}"
else
    echo -e "${RED}1. 修复失败的检查项${NC}"
    echo -e "${YELLOW}2. 重新运行验证脚本${NC}"
    echo -e "${YELLOW}3. 确保所有检查都通过${NC}"
    echo -e "${YELLOW}4. 然后开始使用新结构${NC}"
fi

echo ""
echo -e "${BLUE}📋 验证完成${NC}"
echo "结束时间: $(date)"
echo ""

# 退出状态
if [ $FAILED_CHECKS -eq 0 ]; then
    exit 0
else
    exit 1
fi
