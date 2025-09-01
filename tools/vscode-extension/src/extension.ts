import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { exec } from 'child_process';

export function activate(context: vscode.ExtensionContext) {
    console.log('Formal Model extension is now active!');

    // 注册编译命令
    let compileDisposable = vscode.commands.registerCommand('formalModel.compile', () => {
        compileDSL();
    });

    // 注册验证命令
    let validateDisposable = vscode.commands.registerCommand('formalModel.validate', () => {
        validateModel();
    });

    // 注册文档生成命令
    let docsDisposable = vscode.commands.registerCommand('formalModel.generateDocs', () => {
        generateDocs();
    });

    context.subscriptions.push(compileDisposable, validateDisposable, docsDisposable);
}

function compileDSL() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showErrorMessage('No active editor');
        return;
    }

    const document = editor.document;
    if (document.languageId !== 'formalmodel') {
        vscode.window.showErrorMessage('Current file is not a Formal Model DSL file');
        return;
    }

    const filePath = document.fileName;
    const outputDir = path.join(path.dirname(filePath), 'generated');

    // 获取Python解释器路径
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Compiling DSL...",
        cancellable: false
    }, async (progress) => {
        try {
            // 检查CLI工具是否存在
            const cliPath = path.join(__dirname, '..', '..', 'formal_model_cli.py');
            if (!fs.existsSync(cliPath)) {
                vscode.window.showErrorMessage('CLI tool not found. Please ensure formal_model_cli.py is available.');
                return;
            }

            // 执行编译命令
            const command = `python "${cliPath}" compile "${filePath}" -o "${outputDir}"`;
            
            exec(command, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Compilation failed: ${error.message}`);
                    return;
                }

                if (stderr) {
                    vscode.window.showWarningMessage(`Compilation warnings: ${stderr}`);
                }

                vscode.window.showInformationMessage(`Compilation successful! Output: ${outputDir}`);
                
                // 打开输出目录
                vscode.commands.executeCommand('vscode.openFolder', vscode.Uri.file(outputDir));
            });

        } catch (error) {
            vscode.window.showErrorMessage(`Compilation error: ${error}`);
        }
    });
}

function validateModel() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showErrorMessage('No active editor');
        return;
    }

    const document = editor.document;
    const filePath = document.fileName;

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Validating model...",
        cancellable: false
    }, async (progress) => {
        try {
            const cliPath = path.join(__dirname, '..', '..', 'formal_model_cli.py');
            if (!fs.existsSync(cliPath)) {
                vscode.window.showErrorMessage('CLI tool not found. Please ensure formal_model_cli.py is available.');
                return;
            }

            const command = `python "${cliPath}" validate "${filePath}"`;
            
            exec(command, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Validation failed: ${error.message}`);
                    return;
                }

                if (stdout.includes('✅')) {
                    vscode.window.showInformationMessage('Model validation passed!');
                } else {
                    vscode.window.showErrorMessage('Model validation failed!');
                }
            });

        } catch (error) {
            vscode.window.showErrorMessage(`Validation error: ${error}`);
        }
    });
}

function generateDocs() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showErrorMessage('No active editor');
        return;
    }

    const document = editor.document;
    const filePath = document.fileName;
    const outputFile = path.join(path.dirname(filePath), `${path.basename(filePath, path.extname(filePath))}_docs.md`);

    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Generating documentation...",
        cancellable: false
    }, async (progress) => {
        try {
            const cliPath = path.join(__dirname, '..', '..', 'formal_model_cli.py');
            if (!fs.existsSync(cliPath)) {
                vscode.window.showErrorMessage('CLI tool not found. Please ensure formal_model_cli.py is available.');
                return;
            }

            const command = `python "${cliPath}" docs "${filePath}" -o "${outputFile}"`;
            
            exec(command, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Documentation generation failed: ${error.message}`);
                    return;
                }

                if (stdout.includes('📄')) {
                    vscode.window.showInformationMessage(`Documentation generated: ${outputFile}`);
                    
                    // 打开生成的文档
                    vscode.workspace.openTextDocument(outputFile).then(doc => {
                        vscode.window.showTextDocument(doc);
                    });
                } else {
                    vscode.window.showErrorMessage('Documentation generation failed!');
                }
            });

        } catch (error) {
            vscode.window.showErrorMessage(`Documentation generation error: ${error}`);
        }
    });
}

export function deactivate() {
    console.log('Formal Model extension is now deactivated!');
}
