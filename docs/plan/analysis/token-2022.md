# Token-2022 与「v3」

官方没有单独的 Token v3 程序。两个部署：

| 名 | Program id | 角色 |
|---|---|---|
| Token（legacy） | `TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA` | 指令 0–24 |
| Token-2022 / Token Extensions | `TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb` | 0–24 字节对字节相同；新指令从 25 起 |

Mint 前 82B、Account 前 165B 布局相同。扩展是 165 之后的 TLV。ATA 程序已经能为两个 Token 程序开账户。

## 本仓怎么开

### 切片 A（已完成）

同一套 classic recipe（`TransferChecked` / `MintToChecked` / `InitAccount3` …），`programIx` 指向外层 Token-2022 账户，而不是 Token。指令 data 0–24 不变。

当前独立 `Token2022` 程序钉住 `TransferChecked` tag 12 和 Token-2022 program account。
`CpiMeta.expectedDataLen` 通用约束要求 Mint=82B、Token Account=165B；发射器在 CPI 前检查，
不解析 Token-2022，也不在 emitter 中写 program-specific 分支。抽取 Runtime wrapper 已按命名空间
统一展开，不再因为增加 recipe 修改名字白名单。

fail-closed：

- mint / account 带 transfer hook（要 remaining accounts）
- transfer fee mint（实际到账 ≠ data 里的 amount）
- permanent delegate / closeable mint 再初始化
- confidential transfer

以上 extension 都会扩展 TLV 账户长度，因此当前 base-layout wrapper 全部在 CPI 前拒绝。Mollusk
已用真实 transfer-fee / enabled transfer-hook mint 验证原子失败。

### 切片 B（要 remaining accounts）

transfer hook 的 extra account metas。本仓 CPI 仍是编译期钉死账户表，开这个等于开运行时 remaining accounts。在那之前，带 hook 的 mint 拒绝。

### 切片 C（要 TLV 读）

transfer fee、interest-bearing、pausable、scaled UI amount。要读 165 之后的 TLV。本仓账户 data 叶还是定长 u64。

## 不叫 v3

文档和任务里写 Token-2022。不要再发明 Token v3 程序 id。

## 和 Phoenix

Phoenix 成交继续走 classic `tokenTransferChecked`。Token-2022 切片先用独立例子钉 `programIx`，不要把两种 program id 塞进同一个 Program。
