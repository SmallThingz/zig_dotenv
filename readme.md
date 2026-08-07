# dotenv
Load ENV vars from `.env` file at runtime or comptime. As fast as my brain could handle.
Tested with `0.16.0`, other versions may work as well. The `0.15` tag preserves the Zig 0.15-compatible release.

This library provides functions for loading environment variables from `.env` files at runtime.
It supports unquoting and unescaping of string values (including substitutions like `${VAR}`), comments, multiline values, and flexible customization via `ParseOptions`.

This library provides functions for loading and parsing environment variables from `.env` files both at runtime and at compile time.

## Installation

```bash
zig fetch --save git+https://github.com/ItsMeSamey/zig_dotenv#main
```

Then, add it to your `build.zig`:

```zig
const dotenv = b.dependency("dotenv", .{});
exe.root_module.addImport("dotenv", dotenv.module("dotenv"));
```

## 🚨🚨 Microlibrary 🚨🚨

This is a microlibrary. The code is mostly straightforward. Consider simply copying `dotenv.zig` directly into your project instead of adding a dependency.
It's only about 1k lines of code (including tests). The choice is yours.

## Usage
Every function returns an immutable hashmap of key/value pairs.
The library uses it's own version of hashmap (see comments in the source for reasoning).
You can also get a mutable version by calling `dotenv.GetParser(options).parse(allocator, data)`.

### Runtime Parsing

```zig
const std = @import("std");
const dotenv = @import("dotenv");

var env: dotenv.EnvType = undefined;

pub fn main() !void {
  var gpa = std.heap.GeneralPurposeAllocator(.{}){};
  defer _ = gpa.deinit();
  const allocator = gpa.allocator();

  // Load and parse the .env file at runtime.
  env = try dotenv.load(allocator, .{});
  defer env.deinit(allocator);

  // Access individual values.
  if (env.get("MY_VARIABLE")) |value| {
    std.debug.print("MY_VARIABLE: {s}\n", .{value});
  }
}
```

### Comptime Parsing

every function for loading has a `Comptime` variant.

```zig
const std = @import("std");
const env = @import("dotenv");

// Loads the .env file at comptime
const env = try env.loadComptime(options);

// Access a value at comptime
const db_url = env.get("DATABASE_URL") orelse "!fallback!";

pub fn main() !void {
  std.debug.print("DATABASE_URL: {s}\n", .{db_url});
}
```

You can also load from a specific file or raw data:

```zig
// From a specific file.
var env = try dotenv.loadFrom("filename.env", allocator, .{});

// From raw data (e.g., embedded or read elsewhere).
const raw_data = "MY_VAR=value\n";
var env = try dotenv.loadFromData(raw_data, allocator, .{});
const env_comptime = comptime try dotenv.loadFromDataComptime(raw_data, allocator, .{});
```

### Iterating over Environment Variables

```zig
const std = @import("std");
const dotenv = @import("dotenv");

pub fn main() !void {
  var gpa = std.heap.GeneralPurposeAllocator(.{}){};
  defer _ = gpa.deinit();
  const allocator = gpa.allocator();

  var env = try dotenv.load(allocator, .{});
  defer env.deinit(allocator);

  var iter = env.iterator();
  while (iter.next()) |entry| {
    std.debug.print("{s}={s}\n", .{ entry.key, entry.value });
  }
}
```

### Error Handling

Runtime functions return `ParseError` (including `ParseValueError`, file I/O errors).
Use `try` or handle explicitly. Errors log details (unless disabled) with line/column numbers.

## Example `.env` File

```
# This is a comment
NOTHING=# This is also a comment, NOTHING is empty string
NOTHING = "" # You can override values
HOSTNAME = localhost
PORT = 8080
URL = http://${HOSTNAME}:${PORT} # Substitutions expand
LITERAL = '${This Will Not Be Substituted}' # But not in single quotes
ESCAPE_SEQUENCES = "\xff\n\r\v\f" # Escapes unescaped (only in double quotes)
MULTILINE_VALUE = "Multi
line# NOT A COMMENT
    value"
UNQUOTED_MULTILINE = Multi\
line\
    value # comments are allowed here but not after the `\`
```

> [!NOTE]
> Comments are not allowed after the `\` character in unquoted values, or the newline will not be escaped.
> ``UNQUOTED_MULTILINE = Multi\ #Comment`` will be parsed as `UNQUOTED_MULTILINE` = `Multi\`, then the next line will cause a parsing error.
> If you put a space after the `\` character, the same will happen, the value will be parsed as a single line.


## How it Works
- **Keys**: Default key validation: First char is alphabetic or `_`; subsequent chars are alphanumeric or `_`.
- **Parsing**: Keys/values split on first `=`.
- **Values**: Supports unquoting and unescaping of string values (including substitutions like `${VAR}`), comments, multiline values, and flexible customization via `ParseOptions`.
- **Verbose Errors**: Detailed logging is provided iff there is a parsing error. The logging can be disabled by specifying `.{ .log_fn = ParseOptions.NopLogFn }`.

## Parsing specification

The parser follows a specification inspired by common `.env` formats (e.g., dotenv), with extensions for Zig efficiency.
It processes the file line-by-line but supports multiline quoted values. Whitespace includes spaces, tabs, vertical tabs (`\v`), form feeds (`\f`), and carriage returns (`\r`). Newlines (`\n` or `\r\n`) advance the line counter.

### General Rules
- **Comments**: Lines starting with `#` (after leading whitespace) are ignored. Inline `#` after a value, and outside of any quotes starts a comment to the end of the line.
- **Key-Value Pairs**: Split on the first `=` (after key). Duplicate keys are overwritten with the last value.
- **Positions**: Errors report 1-based line and column numbers, with a caret (`^`) marker and up to 100 chars of context (configurable via `max_error_line_peek`).
- **Encoding**: supports UTF-8 as bytes (no validation or normalization).
- **Windows Line Endings**: supported; `\r\n` treated as newline.

### Keys
- **Format**: `KEY=VALUE` (spaces around `=` optional, trimmed).
- **Validation**: (customizable via `is_valid_first_key_char_fn` and `is_valid_key_char_fn`):
  - **Defaults**
    - First character: Alphabetic (`a-zA-Z`) or `_`.
    - Subsequent characters: Alphanumeric (`a-zA-Z0-9`) or `_`.
- **Errors**: see comments for eash specific error in the source.

### Values
Values start after `=` (leading whitespace trimmed). Parsing mode determined by first non-whitespace char:
- Unquoted (no quote): `\` is used to escape itself and `${`(substitution block). That is `\\` will parse to `\` and `\${VAR}` will not be substituted.
- Single-quoted (`'`): `\` is used to escape itself and `'` (single quote). That is `\\` will parse to `\` and `\'` will parse to `'`.
- Double-quoted (`"`): `\` is used to escape itself, `"` (double quote) and the following escape sequences:
  - **`\n`**: newline.
  - **`\r`**: carriage return.
  - **`\t`**: tab.
  - **`\v`**: vertical tab.
  - **`\f`**: form feed.
  - **`\xHH`**: hex byte (`H` = `0-9a-fA-F`; errors if invalid/partial).
  - **`\${...}`**: substitution block.
  Other escape sequences generate errors (this is not the case for unquoted / single-quoted values).

- Starting with `#`: Empty value (inline comment).
- EOF/Newline: Empty value.

Trailing whitespace after value is trimmed, to preserve whitespace, use quoted values.
`#` starts an inline comment, if you need a `#` in a value, use quoted values.

#### Quoted Values
- **Multiline**: Continues across lines until closing quote (newlines preserved as `\n`).
- **Inline `#`**: Ignored inside quotes (not a comment).
- **Closing**: Trailing whitespace/comments after closing quote ignored.

### Substitutions (`${KEY}`)
- Only in double-quoted or unquoted values.
- `KEY` follows key rules (alphabetic/`_` first, alphanumeric/`_` after).
- Expands to value of prior `KEY` (forward-only, no recursion).
- Single quotes: Literal `${KEY}`.

> [!NOTE]
> unlike bash, only "${VAR}" is substituted, "$VAR" is kept as-is.

### Logging and Customization
- **Logging**: Via `log_fn` (default: `std.debug.print`; `NopLogFn` disables). Logs errors with context.
- **Validation**: Custom `is_valid_first_key_char_fn`/`is_valid_key_char_fn` predicates with signature `fn (u8) bool`; invalid characters are reported through `log_fn`.
- **Peek**: `max_error_line_peek` limits error context.

### Edge Cases (from Tests)
| Case | Behavior | Example |
|------|----------|---------|
| Empty file | Empty map | `""` → `{}` |
| Only comments/whitespace | Empty map | `# comment\n  \n` → `{}` |
| Empty value | `""` | `KEY=` → `""` |
| Trailing newline | Ignored | `KEY=value\n` → `"value"` |
| Duplicate keys | Last wins | `KEY=first\nKEY=second` → `"second"` |
| Inline comment (no space) | Value until `#` | `KEY=val#comment` → `"val"` |
| Escaped quote (single) | Preserved | `'va\'l'` → `"va'l"` |
| Hex escape (double) | Decoded | `"\xFF"` → byte `0xFF` |
| Partial hex | Error | `"\xG"` → `InvalidEscapeSequence` |
| UTF-8/Emoji | Preserved as bytes | `"Hello 😊"` → bytes |
| Export prefix | Invalid key | `export KEY=value` → `InvalidKeyChar` |
| Multiple `=` in value | Preserved | `KEY=val=more` → `"val=more"` |
| Value ending `\` (unquoted) | Literal | `KEY=val\` → `"val\\"` (only one `\`) |
| Value ending `\` (unquoted) | Literal | `KEY=val\\` → `"val\\"` (only one `\`) |
| Value ending `\` (unquoted) | Literal | `KEY=val\\\` → `"val\\\\"` (2 `\`) |
