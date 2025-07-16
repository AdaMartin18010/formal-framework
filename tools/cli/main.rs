//! formal-framework CLI 脚手架主程序
use clap::{Parser, Subcommand};

mod commands;

#[derive(Parser)]
#[command(name = "formal")]
#[command(about = "形式化工程自动化脚手架", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// 初始化新项目
    Init {
        #[arg(short, long)]
        name: Option<String>,
    },
    /// 根据模型定义生成代码/配置/文档
    Generate {
        #[arg(short, long)]
        model: String,
        #[arg(short, long)]
        output: Option<String>,
    },
    /// 插件管理
    Plugin {
        #[arg(subcommand)]
        sub: PluginCmd,
    },
}

#[derive(Subcommand)]
enum PluginCmd {
    /// 列出已安装插件
    List,
    /// 安装插件
    Install { name: String },
    /// 卸载插件
    Uninstall { name: String },
}

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Commands::Init { name } => {
            commands::init::run_init(name);
        }
        Commands::Generate { model, output } => {
            commands::generate::run_generate(&model, output.as_deref());
        }
        Commands::Plugin { sub } => match sub {
            PluginCmd::List => println!("已安装插件: ..."),
            PluginCmd::Install { name } => println!("安装插件: {}", name),
            PluginCmd::Uninstall { name } => println!("卸载插件: {}", name),
        },
    }
} 