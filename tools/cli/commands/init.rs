//! 项目初始化命令实现样例
use std::io::{self, Write};

pub fn run_init(name: Option<String>) {
    let project_name = match name {
        Some(n) => n,
        None => {
            print!("请输入项目名称: ");
            io::stdout().flush().unwrap();
            let mut input = String::new();
            io::stdin().read_line(&mut input).unwrap();
            input.trim().to_string()
        }
    };
    println!("创建项目目录: {}", project_name);
    // TODO: 生成目录结构、模板文件等
    println!("项目初始化完成！");
} 