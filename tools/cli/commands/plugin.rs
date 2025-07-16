//! 插件开发接口与元数据
use std::collections::HashMap;

pub trait Plugin {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn description(&self) -> &str;
    fn execute(&self, args: HashMap<String, String>) -> Result<String, String>;
}

/// 插件元数据（manifest.json）模板
/// {
///   "name": "my-plugin",
///   "version": "0.1.0",
///   "description": "自定义代码生成插件",
///   "entry": "libmy_plugin.so",
///   "author": "your name",
///   "type": "generator|validator|ai|tool",
///   "dependencies": {}
/// }

// 插件开发者需在动态库中导出如下入口（示例）
/*
#[no_mangle]
pub extern "C" fn create_plugin() -> Box<dyn Plugin> {
    Box::new(MyPluginImpl::default())
}
*/ 