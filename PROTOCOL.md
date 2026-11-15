# PvZ Co-op v4 — протокол и игровая часть

Кадр TCP (little-endian): `u16 длина(kind+payload)`, `u8 kind`, payload. Версия протокола 5 (v4 не соединится).

| kind | имя | payload |
|---|---|---|
| 0x01 | HELLO | `u8 ver, u8 роль, char[16] имя` |
| 0x10/0x11 | ADD / REMOVE | `i16 row,col,type,imitater` / `i16 row,col,type` |
| 0x12/0x13 | SUN / SETSUN | `i32` дельта / абсолют |
| 0x14/0x15 | PLANTS / REQ | список растений хоста (F7) / запрос клиента |
| 0x20 | STATE | `i8 scene, i16 mode, i16 level, u8 done, u8 inboard, i32 тик доски, i16 мс на тик` (каждые 0.25 с) |
| 0x21 | CURSOR | `i16 x, y, seed, imitater, cursorType, слот` |
| 0x24 | SLOTS | `u8 n, n×(i16 тип, i16 имитатор)` слоты хоста |
| 0x25 | SLOTUSE | `u8 слот, i16 тип, i16 имитатор, u16 время зарядки` |
| 0x22 | SEEDS | `u8 done, u8 n, n×u8` банк семян хоста; done=1 — хост нажал старт |
| 0x23 | SEEDREQ | `u8 seed, u8 want` (клиент → хост при `seed_choice=both`) |
| 0x30/0x31 | LOSE / WIN | без payload |
| 0x40/0x41/0x50 | PING / PONG / BYE | |

## Игровая часть (PvZ_Coop.CT)
* **00 CORE** — буфер 0x700600–0x700FFF, окно меню, `coop_apply_entry`. Записи: 02 убрать растение, 05 посадить, 06 `Board::ZombiesWon(зомби)` (нужен настоящий зомби: берётся живой, иначе создаётся через `AddZombieInRow`; с нулём игра падала), 07 `Board::FadeOutLevel`, 08/09 выбрать/вернуть семя в `SeedChooserScreen`, 0A `CloseSeedChooser`, 0B/0C/0D запросы (`IsWallnutBowlingLevel`, `HasLevelAwardDropped`, `GetNumSeedsInBank`; ответ в QRES). Стек после каждого вызова восстанавливается из COOP_SAVEESP.
* **01A / 01B** — хук тика (415D40 / 415DF0): применяет записи, сбрасывает флаг паузы (Board+164), держит таймеры старта (559C, 5538), показывает меню.
* **02 NO-PAUSE** — `LawnApp::CanPauseNow` (44F410) всегда отвечает «нельзя»; оригинальные 3 байта читаются при включении и возвращаются при выключении.

Сцены (app+7FC), как приняты в коде: 2 выбор семян/вступление, 3 игра, 4 зомби победили, 5 награда.
