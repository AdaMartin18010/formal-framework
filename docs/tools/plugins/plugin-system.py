#!/usr/bin/env python3
"""
插件生态系统
提供可扩展的插件架构，支持第三方插件开发
"""

import json
import importlib
import inspect
import os
import sys
from typing import Dict, List, Any, Optional, Callable, Type
from dataclasses import dataclass, asdict
from enum import Enum
from pathlib import Path
import zipfile
import shutil


class PluginType(Enum):
    """插件类型"""
    VERIFICATION = "verification"
    VISUALIZATION = "visualization"
    INTEGRATION = "integration"
    ANALYSIS = "analysis"
    EXPORT = "export"
    IMPORT = "import"
    CUSTOM = "custom"


class PluginStatus(Enum):
    """插件状态"""
    INSTALLED = "installed"
    ENABLED = "enabled"
    DISABLED = "disabled"
    ERROR = "error"
    UPDATING = "updating"


@dataclass
class PluginInfo:
    """插件信息"""
    plugin_id: str
    name: str
    version: str
    description: str
    author: str
    plugin_type: PluginType
    dependencies: List[str]
    requirements: List[str]
    entry_point: str
    status: PluginStatus
    install_path: str
    metadata: Dict[str, Any]


@dataclass
class PluginAPI:
    """插件API接口"""
    name: str
    description: str
    parameters: List[Dict[str, Any]]
    return_type: str
    version: str


class PluginManager:
    """插件管理器"""
    
    def __init__(self, plugins_dir: str = "plugins"):
        self.plugins_dir = Path(plugins_dir)
        self.plugins_dir.mkdir(exist_ok=True)
        
        self.plugins: Dict[str, PluginInfo] = {}
        self.loaded_plugins: Dict[str, Any] = {}
        self.plugin_apis: Dict[str, List[PluginAPI]] = {}
        
        self._load_installed_plugins()
    
    def install_plugin(self, plugin_path: str) -> bool:
        """安装插件"""
        try:
            plugin_path = Path(plugin_path)
            
            if plugin_path.suffix == '.zip':
                return self._install_from_zip(plugin_path)
            elif plugin_path.is_dir():
                return self._install_from_directory(plugin_path)
            else:
                print(f"不支持的插件格式: {plugin_path}")
                return False
                
        except Exception as e:
            print(f"安装插件失败: {str(e)}")
            return False
    
    def _install_from_zip(self, zip_path: Path) -> bool:
        """从ZIP文件安装插件"""
        plugin_id = zip_path.stem
        
        # 创建插件目录
        plugin_dir = self.plugins_dir / plugin_id
        plugin_dir.mkdir(exist_ok=True)
        
        # 解压ZIP文件
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            zip_ref.extractall(plugin_dir)
        
        # 读取插件信息
        manifest_path = plugin_dir / "plugin.json"
        if not manifest_path.exists():
            print(f"插件清单文件不存在: {manifest_path}")
            return False
        
        plugin_info = self._load_plugin_manifest(manifest_path)
        if not plugin_info:
            return False
        
        plugin_info.plugin_id = plugin_id
        plugin_info.install_path = str(plugin_dir)
        plugin_info.status = PluginStatus.INSTALLED
        
        self.plugins[plugin_id] = plugin_info
        self._save_plugin_registry()
        
        print(f"插件 {plugin_info.name} 安装成功")
        return True
    
    def _install_from_directory(self, source_dir: Path) -> bool:
        """从目录安装插件"""
        plugin_id = source_dir.name
        
        # 创建插件目录
        plugin_dir = self.plugins_dir / plugin_id
        if plugin_dir.exists():
            shutil.rmtree(plugin_dir)
        
        shutil.copytree(source_dir, plugin_dir)
        
        # 读取插件信息
        manifest_path = plugin_dir / "plugin.json"
        if not manifest_path.exists():
            print(f"插件清单文件不存在: {manifest_path}")
            return False
        
        plugin_info = self._load_plugin_manifest(manifest_path)
        if not plugin_info:
            return False
        
        plugin_info.plugin_id = plugin_id
        plugin_info.install_path = str(plugin_dir)
        plugin_info.status = PluginStatus.INSTALLED
        
        self.plugins[plugin_id] = plugin_info
        self._save_plugin_registry()
        
        print(f"插件 {plugin_info.name} 安装成功")
        return True
    
    def _load_plugin_manifest(self, manifest_path: Path) -> Optional[PluginInfo]:
        """加载插件清单"""
        try:
            with open(manifest_path, 'r', encoding='utf-8') as f:
                manifest = json.load(f)
            
            return PluginInfo(
                plugin_id="",  # 将在调用处设置
                name=manifest.get("name", ""),
                version=manifest.get("version", "1.0.0"),
                description=manifest.get("description", ""),
                author=manifest.get("author", ""),
                plugin_type=PluginType(manifest.get("type", "custom")),
                dependencies=manifest.get("dependencies", []),
                requirements=manifest.get("requirements", []),
                entry_point=manifest.get("entry_point", "main.py"),
                status=PluginStatus.INSTALLED,
                install_path="",  # 将在调用处设置
                metadata=manifest.get("metadata", {})
            )
        except Exception as e:
            print(f"加载插件清单失败: {str(e)}")
            return None
    
    def enable_plugin(self, plugin_id: str) -> bool:
        """启用插件"""
        if plugin_id not in self.plugins:
            print(f"插件 {plugin_id} 不存在")
            return False
        
        plugin_info = self.plugins[plugin_id]
        
        # 检查依赖
        if not self._check_dependencies(plugin_info):
            return False
        
        # 加载插件
        if not self._load_plugin(plugin_info):
            return False
        
        plugin_info.status = PluginStatus.ENABLED
        self._save_plugin_registry()
        
        print(f"插件 {plugin_info.name} 已启用")
        return True
    
    def disable_plugin(self, plugin_id: str) -> bool:
        """禁用插件"""
        if plugin_id not in self.plugins:
            print(f"插件 {plugin_id} 不存在")
            return False
        
        plugin_info = self.plugins[plugin_id]
        
        # 卸载插件
        if plugin_id in self.loaded_plugins:
            del self.loaded_plugins[plugin_id]
        
        plugin_info.status = PluginStatus.DISABLED
        self._save_plugin_registry()
        
        print(f"插件 {plugin_info.name} 已禁用")
        return True
    
    def uninstall_plugin(self, plugin_id: str) -> bool:
        """卸载插件"""
        if plugin_id not in self.plugins:
            print(f"插件 {plugin_id} 不存在")
            return False
        
        plugin_info = self.plugins[plugin_id]
        
        # 禁用插件
        self.disable_plugin(plugin_id)
        
        # 删除插件目录
        plugin_dir = Path(plugin_info.install_path)
        if plugin_dir.exists():
            shutil.rmtree(plugin_dir)
        
        # 从注册表中移除
        del self.plugins[plugin_id]
        self._save_plugin_registry()
        
        print(f"插件 {plugin_info.name} 已卸载")
        return True
    
    def _check_dependencies(self, plugin_info: PluginInfo) -> bool:
        """检查插件依赖"""
        for dep in plugin_info.dependencies:
            if dep not in self.plugins:
                print(f"缺少依赖插件: {dep}")
                return False
            
            dep_plugin = self.plugins[dep]
            if dep_plugin.status != PluginStatus.ENABLED:
                print(f"依赖插件 {dep} 未启用")
                return False
        
        return True
    
    def _load_plugin(self, plugin_info: PluginInfo) -> bool:
        """加载插件"""
        try:
            plugin_dir = Path(plugin_info.install_path)
            entry_file = plugin_dir / plugin_info.entry_point
            
            if not entry_file.exists():
                print(f"插件入口文件不存在: {entry_file}")
                return False
            
            # 添加插件目录到Python路径
            if str(plugin_dir) not in sys.path:
                sys.path.insert(0, str(plugin_dir))
            
            # 动态导入插件模块
            module_name = plugin_info.entry_point.replace('.py', '')
            module = importlib.import_module(module_name)
            
            # 检查插件是否实现了必要的接口
            if not self._validate_plugin_interface(module, plugin_info):
                return False
            
            self.loaded_plugins[plugin_info.plugin_id] = module
            self._extract_plugin_apis(plugin_info, module)
            
            return True
            
        except Exception as e:
            print(f"加载插件失败: {str(e)}")
            plugin_info.status = PluginStatus.ERROR
            return False
    
    def _validate_plugin_interface(self, module: Any, plugin_info: PluginInfo) -> bool:
        """验证插件接口"""
        # 检查必要的函数或类
        required_interface = {
            PluginType.VERIFICATION: ["verify", "get_verification_info"],
            PluginType.VISUALIZATION: ["visualize", "get_visualization_options"],
            PluginType.INTEGRATION: ["integrate", "get_integration_info"],
            PluginType.ANALYSIS: ["analyze", "get_analysis_options"],
            PluginType.EXPORT: ["export", "get_export_formats"],
            PluginType.IMPORT: ["import_data", "get_import_formats"],
            PluginType.CUSTOM: ["execute", "get_plugin_info"]
        }
        
        required_methods = required_interface.get(plugin_info.plugin_type, ["execute"])
        
        for method in required_methods:
            if not hasattr(module, method):
                print(f"插件缺少必要方法: {method}")
                return False
        
        return True
    
    def _extract_plugin_apis(self, plugin_info: PluginInfo, module: Any):
        """提取插件API"""
        apis = []
        
        # 获取模块中的所有函数和类
        for name, obj in inspect.getmembers(module):
            if inspect.isfunction(obj) or inspect.isclass(obj):
                api = PluginAPI(
                    name=name,
                    description=getattr(obj, '__doc__', '') or '',
                    parameters=self._extract_parameters(obj),
                    return_type=str(type(obj).__name__),
                    version=plugin_info.version
                )
                apis.append(api)
        
        self.plugin_apis[plugin_info.plugin_id] = apis
    
    def _extract_parameters(self, obj: Any) -> List[Dict[str, Any]]:
        """提取参数信息"""
        try:
            sig = inspect.signature(obj)
            parameters = []
            
            for param_name, param in sig.parameters.items():
                param_info = {
                    "name": param_name,
                    "type": str(param.annotation) if param.annotation != inspect.Parameter.empty else "Any",
                    "default": str(param.default) if param.default != inspect.Parameter.empty else None,
                    "required": param.default == inspect.Parameter.empty
                }
                parameters.append(param_info)
            
            return parameters
        except:
            return []
    
    def call_plugin_method(self, plugin_id: str, method_name: str, *args, **kwargs) -> Any:
        """调用插件方法"""
        if plugin_id not in self.loaded_plugins:
            raise ValueError(f"插件 {plugin_id} 未加载")
        
        plugin_module = self.loaded_plugins[plugin_id]
        
        if not hasattr(plugin_module, method_name):
            raise ValueError(f"插件 {plugin_id} 没有方法 {method_name}")
        
        method = getattr(plugin_module, method_name)
        return method(*args, **kwargs)
    
    def get_plugin_list(self) -> List[PluginInfo]:
        """获取插件列表"""
        return list(self.plugins.values())
    
    def get_enabled_plugins(self) -> List[PluginInfo]:
        """获取已启用的插件列表"""
        return [p for p in self.plugins.values() if p.status == PluginStatus.ENABLED]
    
    def get_plugins_by_type(self, plugin_type: PluginType) -> List[PluginInfo]:
        """根据类型获取插件"""
        return [p for p in self.plugins.values() if p.plugin_type == plugin_type]
    
    def get_plugin_apis(self, plugin_id: str) -> List[PluginAPI]:
        """获取插件API列表"""
        return self.plugin_apis.get(plugin_id, [])
    
    def _load_installed_plugins(self):
        """加载已安装的插件"""
        registry_file = self.plugins_dir / "plugin_registry.json"
        
        if registry_file.exists():
            try:
                with open(registry_file, 'r', encoding='utf-8') as f:
                    registry = json.load(f)
                
                for plugin_data in registry.get("plugins", []):
                    plugin_info = PluginInfo(**plugin_data)
                    plugin_info.plugin_type = PluginType(plugin_info.plugin_type)
                    plugin_info.status = PluginStatus(plugin_info.status)
                    self.plugins[plugin_info.plugin_id] = plugin_info
                    
                    # 如果插件是启用状态，尝试加载
                    if plugin_info.status == PluginStatus.ENABLED:
                        self._load_plugin(plugin_info)
                        
            except Exception as e:
                print(f"加载插件注册表失败: {str(e)}")
    
    def _save_plugin_registry(self):
        """保存插件注册表"""
        registry_file = self.plugins_dir / "plugin_registry.json"
        
        registry = {
            "plugins": [asdict(plugin) for plugin in self.plugins.values()],
            "timestamp": str(datetime.datetime.now())
        }
        
        with open(registry_file, 'w', encoding='utf-8') as f:
            json.dump(registry, f, indent=2, ensure_ascii=False, default=str)


def create_sample_plugin(plugin_dir: str, plugin_info: Dict[str, Any]):
    """创建示例插件"""
    plugin_path = Path(plugin_dir)
    plugin_path.mkdir(exist_ok=True)
    
    # 创建插件清单
    manifest = {
        "name": plugin_info.get("name", "Sample Plugin"),
        "version": plugin_info.get("version", "1.0.0"),
        "description": plugin_info.get("description", "示例插件"),
        "author": plugin_info.get("author", "Plugin Developer"),
        "type": plugin_info.get("type", "custom"),
        "dependencies": plugin_info.get("dependencies", []),
        "requirements": plugin_info.get("requirements", []),
        "entry_point": "main.py",
        "metadata": plugin_info.get("metadata", {})
    }
    
    with open(plugin_path / "plugin.json", 'w', encoding='utf-8') as f:
        json.dump(manifest, f, indent=2, ensure_ascii=False)
    
    # 创建插件主文件
    plugin_code = f'''#!/usr/bin/env python3
"""
{plugin_info.get("name", "Sample Plugin")}
{plugin_info.get("description", "示例插件")}
"""

def execute(data=None, options=None):
    """
    执行插件功能
    
    Args:
        data: 输入数据
        options: 选项参数
    
    Returns:
        处理结果
    """
    print("执行示例插件...")
    return {{
        "status": "success",
        "message": "插件执行完成",
        "data": data,
        "options": options
    }}

def get_plugin_info():
    """
    获取插件信息
    
    Returns:
        插件信息字典
    """
    return {{
        "name": "{plugin_info.get("name", "Sample Plugin")}",
        "version": "{plugin_info.get("version", "1.0.0")}",
        "description": "{plugin_info.get("description", "示例插件")}",
        "author": "{plugin_info.get("author", "Plugin Developer")}"
    }}

if __name__ == "__main__":
    # 测试插件
    result = execute("test data", {{"option1": "value1"}})
    print(result)
'''
    
    with open(plugin_path / "main.py", 'w', encoding='utf-8') as f:
        f.write(plugin_code)
    
    print(f"示例插件已创建: {plugin_path}")


def main():
    """主函数 - 演示插件系统"""
    manager = PluginManager()
    
    print("=== 正式验证框架插件系统演示 ===")
    
    # 创建示例插件
    sample_plugin_info = {
        "name": "示例验证插件",
        "version": "1.0.0",
        "description": "一个示例验证插件",
        "author": "插件开发者",
        "type": "verification",
        "dependencies": [],
        "requirements": [],
        "metadata": {
            "category": "example",
            "tags": ["sample", "verification"]
        }
    }
    
    create_sample_plugin("sample_plugin", sample_plugin_info)
    
    # 安装插件
    if manager.install_plugin("sample_plugin"):
        print("插件安装成功")
        
        # 启用插件
        if manager.enable_plugin("sample_plugin"):
            print("插件启用成功")
            
            # 调用插件方法
            try:
                result = manager.call_plugin_method("sample_plugin", "execute", "测试数据")
                print(f"插件执行结果: {result}")
                
                info = manager.call_plugin_method("sample_plugin", "get_plugin_info")
                print(f"插件信息: {info}")
                
            except Exception as e:
                print(f"调用插件方法失败: {str(e)}")
    
    # 显示插件列表
    plugins = manager.get_plugin_list()
    print(f"\n已安装插件数量: {len(plugins)}")
    
    for plugin in plugins:
        print(f"  - {plugin.name} ({plugin.plugin_id}) - {plugin.status.value}")
    
    # 显示插件API
    apis = manager.get_plugin_apis("sample_plugin")
    print(f"\n插件API数量: {len(apis)}")
    
    for api in apis:
        print(f"  - {api.name}: {api.description}")


if __name__ == "__main__":
    main()
