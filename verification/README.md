# 本轮验证的范围

本目录中的 `results.json`、`build.log`、`audit195-unconditional.log` 由
[`scripts/verify-upstream.ps1`](../scripts/verify-upstream.ps1) 实际执行生成。

上游固定提交：`2e91b05b25a4ee931a0490fefcdbb4f253be95c8`。
Lean：`4.35.0-rc4`；mathlib 固定版本由上游 `lake-manifest.json` 指定。

本次使用此前已有编译缓存的本地上游工程，先比较其 75 个 Lean 文件和
4 个环境/启动文件与固定子模块源码是否逐字节相同，再运行：

```text
lake build
lake env lean StrongEdge/Audit195Unconditional.lean
```

脚本保存原始输出、实际退出码、逐文件 SHA-256、公理审计结果，并在运行后
再次确认这 79 个文件未改变。公理允许列表只有 `propext`、`Classical.choice`、`Quot.sound`。
审计条目与审计源码的 `#print axioms` 名称逐项匹配，解析包括跨行公理列表。

这是**已有工程的增量构建及本轮公理审计**，不是从空缓存重新编译所有依赖，
也不是对新研究结论的 Lean 认证。没有新增 `sorry`、`admit` 或数学公理。

第一个参数可指向字节一致且已准备好依赖的另一份上游 `lean/` 目录。
省略它则使用本仓库子模块中的 `lean/`；干净子模块需要先按上游说明准备依赖缓存。
工具链参数可省略，但届时 `lean` 和 `lake` 必须已在 `PATH` 上。

```powershell
./scripts/verify-upstream.ps1 -ProjectDirectory 'C:/path/to/packing195/lean' -ToolchainBin 'C:/path/to/lean-4.35.0-rc4-windows/bin'
```

本轮没有运行 39 边原图搜索；日志不能支持“已排除 k=2”或“已证明 19 倍界”的说法。
