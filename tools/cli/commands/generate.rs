//! generate命令实现样例
use std::fs;

pub fn run_generate(model: &str, output: Option<&str>) {
    println!("读取模型定义: {}", model);
    // TODO: 解析模型，调用生成器
    let code = format!("// 根据模型 {} 生成的代码\nfn main() {{ println!(\"Hello, world!\"); }}", model);
    let out_path = output.unwrap_or("generated/main.rs");
    fs::create_dir_all("generated").unwrap();
    fs::write(out_path, code).unwrap();
    println!("代码已生成: {}", out_path);
} 