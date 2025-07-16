//! AI推理引擎trait定义

pub trait ReasoningEngine {
    /// 输入模型定义，输出推理建议或优化结果
    fn analyze(&self, model: &str) -> Result<String, ReasoningError>;
}

#[derive(Debug)]
pub enum ReasoningError {
    InvalidModel(String),
    LlmError(String),
    Other(String),
} 