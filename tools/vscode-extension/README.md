# Formal Model VS Code Extension

Formal Model DSL support for Visual Studio Code.

## Features

- **Syntax Highlighting**: Full syntax highlighting for Formal Model DSL files
- **Code Snippets**: Predefined snippets for common DSL constructs
- **Compilation**: Direct compilation of DSL files to target languages
- **Validation**: Model validation with error reporting
- **Documentation Generation**: Automatic documentation generation from models

## Installation

1. Clone this repository
2. Install dependencies:

   ```bash
   npm install
   ```

3. Compile the extension:

   ```bash
   npm run compile
   ```

4. Press F5 to run the extension in a new Extension Development Host window

## Usage

### File Extensions

The extension supports files with the following extensions:

- `.fm` - Formal Model files
- `.dsl` - DSL files

### Commands

#### Compile DSL

Compiles the current DSL file to target language code.

**Command Palette**: `Formal Model: Compile DSL`
**Context Menu**: Right-click in editor → "Compile DSL"

#### Validate Model

Validates the current model file for syntax and semantic correctness.

**Command Palette**: `Formal Model: Validate Model`
**Context Menu**: Right-click in editor → "Validate Model"

#### Generate Documentation

Generates Markdown documentation from the current model file.

**Command Palette**: `Formal Model: Generate Documentation`
**Context Menu**: Right-click in editor → "Generate Documentation"

### Code Snippets

| Snippet | Description |
|---------|-------------|
| `model` | Create a new model definition |
| `entity` | Create a new entity definition |
| `operation` | Create a new operation definition |
| `attr` | Create a new attribute definition |
| `param` | Create a new parameter definition |
| `string` | String type |
| `number` | Number type |
| `boolean` | Boolean type |

## Requirements

- Python 3.7+ with the Formal Model CLI tool installed
- The `formal_model_cli.py` script must be available in the parent directory

## Development

### Project Structure

```text
vscode-extension/
├── src/
│   └── extension.ts          # Main extension code
├── syntaxes/
│   └── formalmodel.tmLanguage.json  # Syntax highlighting
├── snippets/
│   └── formalmodel.json     # Code snippets
├── language-configuration.json  # Language configuration
├── package.json             # Extension manifest
├── tsconfig.json           # TypeScript configuration
└── README.md              # This file
```

### Building

```bash
npm run compile
```

### Testing

```bash
npm test
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests if applicable
5. Submit a pull request

## License

MIT License
