# VeriST 清理规则说明

## Makefile 清理目标

### 主目录 (/home/wei/coq/Makefile)

#### `make clean`
清理所有编译产物，但保留源代码文件。

**清理内容：**
- Coq 编译产物：`*.vo`, `*.vok`, `*.vos`, `*.glob`, `.*.aux`
- OCaml 编译产物：`*.cmo`, `*.cmi`, `*.cmx`, `*.o`, `*.cmt`, `*.cmti`
- Coq 生成的 Makefile：`Makefile.coq`, `Makefile.coq.conf`
- Dune 构建目录：`_build/`
- extraction 目录中的编译产物

**保留内容：**
- 所有源代码（`.v`, `.ml`, `.mli` 文件）
- 配置文件（`_CoqProject`）

#### `make cleanall`
深度清理，包括移除提取的 OCaml 源代码。

**额外清理：**
- 根目录的 `*.ml`, `*.mli` 文件
- extraction 目录中的所有 `*.ml`, `*.mli` 文件

**注意：** 运行 `cleanall` 后需要重新运行 `make` 来重新生成提取的代码。

---

### extraction 目录 (/home/wei/coq/extraction/Makefile)

#### `make clean`
清理编译产物和生成的文件。

**清理内容：**
- OCaml 编译产物：`*.cmo`, `*.cmi`, `*.cmx`, `*.o`
- 编译信息文件：`*.cmt`, `*.cmti`, `*.cma`, `*.cmxa`, `*.a`
- 可执行文件：`veriST`, `veriST.opt`
- Parser/Lexer 生成文件：`lexer.ml`, `parser.ml`, `parser.mli`, `parser.output`, `parser.conflicts`
- 字节码文件：`*.stbc`

**保留内容：**
- 源代码：`*.ml`, `*.mli` (提取的和手写的)
- Parser/Lexer 源文件：`parser.mly`, `lexer.mll`

#### `make cleanall`
深度清理，包括移除所有提取的源代码。

**额外清理：**
- 所有 `*.ml`, `*.mli` 文件

---

## 使用示例

### 标准清理工作流
```bash
# 在主目录
cd /home/wei/coq
make clean          # 清理编译产物
make                # 重新编译 Coq 理论

# 在 extraction 目录
cd extraction
make clean          # 清理 OCaml 编译产物
./build.sh          # 重新编译编译器
```

### 完全重建工作流
```bash
# 从头开始重建
cd /home/wei/coq
make cleanall       # 深度清理
make                # 重新生成所有文件
cd extraction
./build.sh          # 编译编译器
```

---

## 清理的文件类型说明

| 扩展名 | 说明 | 清理级别 |
|--------|------|----------|
| `.vo`, `.vok`, `.vos` | Coq 编译对象文件 | clean |
| `.glob`, `.aux` | Coq 辅助文件 | clean |
| `.cmo`, `.cmi` | OCaml 字节码编译文件 | clean |
| `.cmx`, `.o` | OCaml 原生代码编译文件 | clean |
| `.cmt`, `.cmti` | OCaml 类型信息文件 | clean |
| `lexer.ml`, `parser.ml` | Parser/Lexer 生成文件 | clean |
| `.stbc` | 编译的字节码文件 | clean |
| `.ml`, `.mli` (提取的) | Coq 提取的 OCaml 源码 | cleanall |

---

更新日期：2025年11月12日
