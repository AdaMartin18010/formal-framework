//! LLM推理接口定义

pub trait LlmProvider {
    /// 发送prompt并获取AI回复
    fn infer(&self, prompt: &str, max_tokens: usize, temperature: f32) -> Result<String, LlmError>;

    /// 支持流式推理（可选）
    fn infer_stream(&self, prompt: &str, max_tokens: usize, temperature: f32) -> Result<Box<dyn Iterator<Item=String>>, LlmError> {
        Err(LlmError::NotImplemented)
    }
}

#[derive(Debug)]
pub enum LlmError {
    Network(String),
    Api(String),
    NotImplemented,
    Other(String),
} 