const std = @import("std");

pub const ParseOptions = struct {
  /// The logging function to use when priniting errors
  /// Set this to `NopLogFn` to disable logging
  log_fn: fn (comptime format: []const u8, args: anytype) void = DefaultLogFn,
  /// The function used to determine if the first character of a key is valid
  is_valid_first_key_char_fn: fn (self: @This(), char: u8) bool = DefaultIsValidFirstKeyChar,
  /// The function used to determine if any other character of a key is valid
  is_valid_key_char_fn: fn (self: @This(), char: u8) bool = DefaultIsValidKeyChar,
  /// How many characters to print after the point at which the error occurred in parsing
  /// This cap is only applied if there is no newline uptile next `max_error_line_peek` characters
  max_error_line_peek: usize = 100,

  const Self = @This();

  /// This is the default logging function
  /// It generates a compile log statement at comptime
  /// It logs to stderr (unbuffered) at runtime
  pub const DefaultLogFn = struct {
    fn log_fn(comptime format: []const u8, args: anytype) void {
      if (@inComptime()) {
        @compileLog(std.fmt.comptimePrint(format, args));
      } else {
        std.debug.print(format, args);
      }
    }
  }.log_fn;

  /// No-op logging function
  /// This does NOT log to @compileLog and does not cause a compile error directly.
  /// At comptime, the parsing function will return an error that can be handled as well
  pub const NopLogFn = struct {
    fn log_fn(comptime _: []const u8, _: anytype) void {}
  }.log_fn;

  /// The default function to determine if the first character of a key is valid
  /// matches [a-zA-Z_]
  pub const DefaultIsValidFirstKeyChar = struct {
    fn is_valid_first_key_char(self: Self, char: u8) bool {
      const is_valid = std.ascii.isAlphabetic(char) or char == '_';
      if (!is_valid) self.log_fn("First character for key should be [a-zA-Z_]; got: `{c}`\n", .{char});
      return is_valid;
    }
  }.is_valid_first_key_char;

  /// The default function to determine if any other character of a key is valid
  /// matches [a-zA-Z0-9_]
  pub const DefaultIsValidKeyChar = struct {
    fn is_valid_key_char(self: Self, char: u8) bool {
      const is_valid = std.ascii.isAlphanumeric(char) or char == '_';
      if (!is_valid) self.log_fn("Key can only contain [a-zA-Z0-9_]; got: `{c}`\n", .{char});
      return is_valid;
    }
  }.is_valid_key_char;

  /// Just a helper to call the function, for internal use only
  fn is_valid_first_key_char(self: @This(), char: u8) bool {
    return self.is_valid_first_key_char_fn(self, char);
  }

  /// Just a helper to call the function, for internal use only
  fn is_valid_key_char(self: @This(), char: u8) bool {
    return self.is_valid_key_char_fn(self, char);
  }
};

/// Errors specific to parsing keys
pub const ParseKeyError = error{
  /// Thrown when the first character of a key (or substitution key) is not alphabetic (a-zA-Z) or '_'
  InvalidFirstKeyChar,
  /// Thrown when a subsequent character in a key (or substitution key) is not alphanumeric (a-zA-Z0-9) or '_'
  /// Also thrown when the character immediately after optional whitespace following the key is not '=' (e.g., KEY?=value)
  InvalidKeyChar,
  /// Thrown when EOF is reached before finding '=' after parsing a key
  UnexpectedEndOfFile,
};

/// Errors specific to parsing values (includes key errors and allocator errors)
pub const ParseValueError = error{
  /// Thrown when EOF is reached inside a quoted value (' or ") without a closing quote
  UnterminatedQuote,
  /// Thrown in double-quoted values when an escape sequence is invalid:
  /// - \x followed by non-hex digits (0-9a-fA-F), including partial (e.g., \xG or \xGG where G invalid)
  /// - \ followed by an unrecognized character (not \\, \", \$, \n, \r, \t, \v, \f, \x)
  InvalidEscapeSequence,
  /// Thrown when parsing a substitution ${KEY} and EOF is reached before finding the closing '}'
  UnterminatedSubstitutionBlock,
  /// Thrown after parsing a value (quoted or unquoted), when skipping trailing whitespace,
  /// and encountering a non-newline, non-'#' character (e.g., extra text after closing quote like `"value" extra`) 
  UnexpectedCharacter,
  /// Thrown when expanding a substitution ${KEY} and no prior key named KEY exists in the map
  SubstitutionKeyNotFound,
} || ParseKeyError || std.mem.Allocator.Error;

pub const ParseError = ParseValueError || std.fs.File.OpenError || std.fs.File.ReadError;

// Read and parse the `.env` file to a EnvType (hashmap)
/// Caller owns the returned hashmap
pub fn load(allocator: std.mem.Allocator, comptime options: ParseOptions) ParseError!EnvType {
  return loadFrom(".env", allocator, options);
}

/// Read and parse the provided env file to a EnvType (hashmap)
/// Caller owns the returned hashmap
pub fn loadFrom(file_name: []const u8, allocator: std.mem.Allocator, comptime options: ParseOptions) ParseError!EnvType {
  var file = try std.fs.cwd().openFile(file_name, .{});
  const file_data = file.readToEndAlloc(allocator, std.math.maxInt(usize)) catch |e| {
    file.close();
    return e;
  };
  file.close();
  defer allocator.free(file_data);

  return loadFromData(file_data, allocator, options);
}

/// Read and parse the provided data string to a EnvType (hashmap)
/// Caller owns the data memory and the returned hashmap
pub fn loadFromData(data: []const u8, allocator: std.mem.Allocator, comptime options: ParseOptions) ParseValueError!EnvType {
  var hm = try GetParser(options).parse(data, allocator);
  defer hm.deinit();
  return .fromHashMap(&hm);
}

// Read and parse the `.env` file to a ComptimeEnvType (actually a hashmap and NOT StaticStringMap)
pub fn loadComptime(options: ParseOptions) ParseValueError!ComptimeEnvType {
  return comptime loadFromComptime(".env", options);
}

/// Read and parse the provided env file to a ComptimeEnvType (actually a hashmap and NOT StaticStringMap)
pub fn loadFromComptime(file_name: []const u8, options: ParseOptions) ParseValueError!ComptimeEnvType {
  return comptime loadFromDataComptime(@embedFile(file_name), options);
}

/// Read and parse the provided data string to a ComptimeEnvType (actually a hashmap and NOT StaticStringMap)
pub fn loadFromDataComptime(file_data: []const u8, options: ParseOptions) ParseValueError!ComptimeEnvType {
  var hm = try GetParser(options).parse(file_data, comptime_allocator);
  return comptime .fromHashMap(&hm);
}

// This is taken from https://github.com/ziglang/zig/issues/1291
pub const comptime_allocator: std.mem.Allocator = struct {
  const allocator: std.mem.Allocator = .{
    .ptr = undefined,
    .vtable = &.{
      .alloc = comptimeAlloc,
      .resize = comptimeResize,
      .remap = comptimeRemap,
      .free = comptimeFree,
    },
  };

  fn comptimeAlloc(_: *anyopaque, len: usize, alignment: std.mem.Alignment, _: usize) ?[*]u8 {
    if (!@inComptime()) unreachable;
    var bytes: [len]u8 align(alignment.toByteUnits()) = undefined;
    return &bytes;
  }

  fn comptimeResize(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) bool {
    // Always returning false here ensures that callsites make new allocations that fit
    // better, avoiding wasted .cdata and .data memory.
    return false;
  }

  fn comptimeRemap(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) ?[*]u8 {
    // Always returning false here ensures that callsites make new allocations that fit
    // better, avoiding wasted .cdata and .data memory.
    return null;
  }

  fn comptimeFree(_: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize) void {
    // Global variables are garbage-collected by the linker.
  }
}.allocator;

/// HashMap implementation used internally while parsing.
/// This is used for key replacement (${...})
/// This is a barebones implementation, it uses 8 bits for the fingerprint
/// unlike the 7 in zig's standard hashmap because we don't require toombstones
///
/// I chose to use write this instead of using the standard hashmap because
/// the standard implementation does not work at comptime, and has toombstones
/// which are not needed for this use case. We would need to use a context variant
/// of the hash map to prevent a new allocation for each value and it would result
/// in same amount of bloat more or less. Besides, this implementation should be
/// slightly faster (hopefully;) and works at comptime as well. Also, converting
/// the standard to ComptimeEnvType / EnvType would need rehashing which this
/// implementation does not need.
pub const HashMap = struct {
  const Size = u32;
  pub const String = packed struct{ idx: usize, len: usize };
  pub const KV = struct { key: []const u8, value: []const u8 };
  const default_max_load_percentage = std.hash_map.default_max_load_percentage;

  // The keys_string
  keys_string: []const u8,
  // The string containing the concatenated values
  values_string: std.ArrayList(u8) = .{},
  // This is the start of our allocated block
  _keys: [*]String = &.{},
  // This comes after the keys
  _values: [*]String = &.{},
  // These will be at the end of our allocated block, 0 means unused.
  _meta: [*]u8 = &.{},
  /// Length for our keys, values, and meta arrays
  cap: Size = 0,
  // How many elements are in use
  size: Size = 0,
  // How many elements are available, this is used to reduce the number of instructions needed for the grow check
  available: Size = 0,
  // The allocator that sores everything
  allocator: std.mem.Allocator,
  // The length of key strings
  // NOTE: this is not the same as keys_string.len as the keys_string contains unused parts
  keys_string_len: usize = 0,

  pub inline fn keys(self: *const @This()) []String { return self._keys[0..self.cap]; }
  pub inline fn values(self: *const @This()) []String { return self._values[0..self.cap]; }
  pub inline fn meta(self: *const @This()) []u8 { return self._meta[0..self.cap]; }

  pub fn init(keys_string: []const u8, cap: Size, allocator: std.mem.Allocator) !@This() {
    @setEvalBranchQuota(1000_000);
    const c = std.math.ceilPowerOfTwo(Size, cap) catch 16;
    const mem = try allocator.alignedAlloc(u8, std.mem.Alignment.of(String), (2 * @sizeOf(String) + 1) * c);
    @memset(mem[2 * c * @sizeOf(String)..], 0);
    return .{
      .keys_string = keys_string,
      ._keys = @alignCast(@ptrCast(mem.ptr)),
      ._values = @alignCast(@ptrCast(mem[c * @sizeOf(String)..].ptr)),
      ._meta = mem[2 * c * @sizeOf(String)..].ptr,
      .cap = c,
      .available = c * default_max_load_percentage / 100,
      .allocator = allocator,
    };
  }

  fn getHFP(key: []const u8) std.meta.Tuple(&.{u64, u8}) {
    const h = std.hash_map.StringContext.hash(undefined, key);
    const fp: u8 = @intCast(h >> 56);
    return .{h, if (fp == 0) 1 else fp};
  }

  fn hashString(self: *const @This(), string: String) u64 {
    return std.hash_map.StringContext.hash(undefined, self.keys_string[string.idx..][0..string.len]);
  }

  fn eqlString(self: *const @This(), string: String, other: []const u8) bool {
    return std.mem.eql(u8, self.keys_string[string.idx..][0..string.len], other);
  }

  fn getIndex(self: *const @This(), fingerprint: u8, hash: u64, key: []const u8) usize {
    var i: usize = @intCast(hash & (self.cap - 1));
    while (self.meta()[i] != 0) : (i = (i + 1) & (self.cap - 1)) {
      if (self.meta()[i] == fingerprint and self.eqlString(self.keys()[i], key)) break;
    }

    return i;
  }

  pub fn get(self: *const @This(), key: []const u8) ?[]const u8 {
    @setEvalBranchQuota(1000_000);
    const hash, const fingerprint = getHFP(key);
    const i = self.getIndex(fingerprint, hash, key);
    if (self.meta()[i] == 0) return null;
    const v = self.values()[i];
    return self.values_string.items[v.idx..][0..v.len];
  }

  pub fn put(self: *@This(), key: String, value: String) !void {
    @setEvalBranchQuota(1000_000);
    try self.grow();

    const kstr = self.keys_string[key.idx..][0..key.len];
    const hash, const fingerprint = getHFP(kstr);
    const i = self.getIndex(fingerprint, hash, kstr);
    if (self.meta()[i] == 0) {
      self.meta()[i] = fingerprint;
      self.keys()[i] = key;
      self.size += 1;
      self.available -= 1;
      self.keys_string_len += key.len;
    }

    self.values()[i] = value;
  }

  fn grow(old: *@This()) !void {
    @setEvalBranchQuota(1000_000);
    if (old.available > old.size) return;
    var self = try init(old.keys_string, if (old.size == 0) 16 else old.size * 2, old.allocator);
    self.values_string = old.values_string;
    self.size = old.size;
    self.keys_string_len = old.keys_string_len;

    for (old.meta(), old.keys(), old.values()) |m, k, v| {
      if (m == 0) continue;
      const kstr = self.keys_string[k.idx..][0..k.len];
      const hash, _ = getHFP(kstr);
      var i: usize = @intCast(hash & (self.cap - 1));
      while (self.meta()[i] != 0) : (i = (i + 1) & (self.cap - 1)) {}
      self.meta()[i] = m;
      self.keys()[i] = k;
      self.values()[i] = v;
    }

    old.allocator.free(old.allocation());
    old.* = self;
  }

  fn allocation(self: *@This()) []align(@alignOf(String)) u8 {
    return @as([*] align(@alignOf(String)) u8, @alignCast(@ptrCast(self._keys)))[0.. (2 * @sizeOf(String) + 1) * self.cap];
  }

  pub fn deinit(self: *@This()) void {
    self.allocator.free(self.allocation());
    self._keys = undefined;
    self._values = undefined;
    self._meta = undefined;
    self.values_string.deinit(self.allocator);
    self.values_string = undefined;
  }
};

/// A type to store the parsed data at comptime, this uses `const` everything to bypass the
/// "runtime values can't hold a reference to a comptime variable" error.
/// 
/// This struct has a smaller size that the HashMap and does not have unused sections in the
/// string (see comment in `fromHashMap`).
/// The key + value size is also reduced to 8 bytes compared to 4*usize (32 if usize = 8) for the HashMap.
pub const ComptimeEnvType = struct {
  const Self = @This();
  const Size = u32;
  pub const KV = HashMap.KV;
  pub const Bucket = struct {
    key_idx: KeyIdxType,
    key_len: KeyLenType,
    const KeyIdxType = std.meta.Int(.unsigned, @min(@bitSizeOf(usize), 40));
    const KeyLenType = std.meta.Int(.unsigned, if (@bitSizeOf(usize) < 40) @bitSizeOf(usize) else 24);
  };

  /// key+value strings concatenated together
  data: []const u8 = &.{},
  /// Buckets of the hashmap
  _buckets: [*]const Bucket = &.{},
  /// Metadata of the hashmap
  _meta: [*]const u8 = &.{},
  /// Capacity of the hashmap
  cap: Size = 0,
  /// How many elements are in use
  size: Size = 0,

  /// Create a new ComptimeEnvType from a HashMap
  pub fn fromHashMap(comptime hm: *HashMap) @This() {
    @setEvalBranchQuota(1000_000);
    comptime {
      var self: @This() = .{ .cap = hm.cap, .size = hm.size };
      var buckets_v: []const Bucket = &.{};
      var meta_v: []const u8 = &.{};

      var last_exists = false;
      for (hm.meta(), hm.keys(), hm.values()) |m, k, v| {
        meta_v = meta_v ++ &[_]u8{m};
        if (m == 0) {
          if (last_exists) {
            buckets_v = buckets_v ++ &[_]Bucket{ .{ .key_idx = @intCast(self.data.len), .key_len = undefined } };
          } else {
            buckets_v = buckets_v ++ &[_]Bucket{undefined};
          }
          last_exists = false;
        } else {
          const ks = hm.keys_string[k.idx..][0..k.len];
          const vs = hm.values_string.items[v.idx..][0..v.len];
          buckets_v = buckets_v ++ &[_]Bucket{ .{ .key_idx = @intCast(self.data.len), .key_len = @intCast(ks.len) } };
          // we re-append to the data because we if any key was overwrite, there would be a unused value string that
          // would not get GC'd (last tested with zig-0.15.1)
          self.data = self.data ++ ks ++ vs;
          last_exists = true;
        }
      }
      std.debug.assert(buckets_v.len == self.cap);
      std.debug.assert(meta_v.len == self.cap);

      buckets_v = buckets_v ++ &[_]Bucket{ .{ .key_idx = @intCast(self.data.len), .key_len = undefined } };
      self._buckets = buckets_v.ptr;
      self._meta = meta_v.ptr;

      return self;
    }
  }

  pub const Iterator = struct {
    map: *const Self,
    i: usize = 0,

    pub fn next(it: *Iterator) ?KV {
      if (it.i >= it.map.capacity()) return null;
      while (it.i < it.map.capacity()) {
        defer it.i += 1;
        if (it.map.meta()[it.i] == 0) continue;
        const bucket = it.map.buckets()[it.i];
        const next_bucket = it.map.buckets()[it.i + 1];
        return .{
          .key = it.map.data[@intCast(bucket.key_idx)..][0..@intCast(bucket.key_len)],
          .value = it.map.data[0..@intCast(next_bucket.key_idx)][@intCast(bucket.key_idx)..][@intCast(bucket.key_len)..]
        };
      }
      return null;
    }
  };

  pub fn iterator(self: *const @This()) Iterator { return .{ .map = self }; }
  pub inline fn count(self: *const @This()) usize { return self.size; }
  pub inline fn capacity(self: *const @This()) usize { return self.cap; }
  pub inline fn buckets(self: *const @This()) []const Bucket { return self._buckets[0..self.cap+1]; }
  pub inline fn meta(self: *const @This()) []const u8 { return self._meta[0..self.cap]; }

  pub fn getRuntime(self: *const @This(), key: []const u8) ?[]const u8 {
    const hash, const fingerprint = HashMap.getHFP(key);
    var i: usize = @intCast(hash & (self.cap - 1));
    while (self.meta()[i] != 0) : (i = (i + 1) & (self.cap - 1)) {
      const bucket = self.buckets()[i];
      if (self.meta()[i] == fingerprint and std.mem.eql(u8, key, self.data[@intCast(bucket.key_idx)..][0..@intCast(bucket.key_len)])) {
        const next = self.buckets()[i + 1];
        return self.data[0..@intCast(next.key_idx)][@intCast(bucket.key_idx)..][@intCast(bucket.key_len)..];
      }
    }

    return null;
  }

  pub fn get(comptime self: *const @This(), comptime key: []const u8) ?[]const u8 {
    return comptime self.getRuntime(key);
  }

  pub fn deinit(comptime self: *@This()) void {
    self.data = undefined;
    self._buckets  = undefined;
    self._meta = undefined;
  }
};

/// A type to store the parsed data at runtime. Stores buckets + metadata + key + value strings
/// in a single allocation.
/// 
/// see comment for `ComptimeEnvType`
pub const EnvType = struct {
  const Size = u32;
  pub const KV = HashMap.KV;
  pub const Bucket = ComptimeEnvType.Bucket;

  /// This is a mid-way pointer, before it is the buckets, after it is the concatenated key + value strings
  _meta: [*]u8 = &.{},
  /// This is the size of the key + value strings region
  _data_size: usize = 0,
  /// This is the size of the buckets / metadata region
  cap: Size = 0,
  /// How many elements are in use
  size: Size = 0,

  /// Caller owns the hashmap
  pub fn fromHashMap(hm: *HashMap) !@This() {
    const allocation_size = (hm.cap + 1) * @sizeOf(Bucket) + hm.cap + (hm.keys_string_len + hm.values_string.items.len);
    var allocation = try hm.allocator.alignedAlloc(u8, std.mem.Alignment.of(Bucket), allocation_size);

    const retval: @This() = .{
      ._meta = allocation[(hm.cap + 1) * @sizeOf(Bucket)..].ptr,
      ._data_size =  hm.keys_string_len + hm.values_string.items.len,
      .size = hm.size,
      .cap = hm.cap,
    };

    const buckets_v = @constCast(retval.buckets());
    const meta_v = @constCast(retval.meta());
    const data_v = @constCast(retval.data());
    var data_idx: usize = 0;
    var last_exists = false;

    for (hm.meta(), hm.keys(), hm.values(), 0..) |m, k, v, i| {
      meta_v[i] = m;
      if (m == 0) {
        if (last_exists) {
          buckets_v[i] = .{ .key_idx = @intCast(data_idx), .key_len = undefined };
        }
        last_exists = false;
      } else {
        const ks = hm.keys_string[k.idx..][0..k.len];
        const vs = hm.values_string.items[v.idx..][0..v.len];
        buckets_v[i] = .{ .key_idx = @intCast(data_idx), .key_len = @intCast(ks.len) };
        @memcpy(data_v[data_idx..][0..ks.len], ks);
        data_idx += ks.len;
        @memcpy(data_v[data_idx..][0..vs.len], vs);
        data_idx += vs.len;
        last_exists = true;
      }
    }

    buckets_v[buckets_v.len - 1] = .{ .key_idx = @intCast(data_idx), .key_len = undefined };

    return retval;
  }

  /// Iterator over the key/value pairs. It stores pointers to the buckets, metadata, and key+value strings
  /// and not the hashmap itself because since hashmap contains a mid-way pointer, it would take more cycles
  /// to derive the buckets and key+value strings from the hashmap.
  pub const Iterator = struct {
    /// Buckets of the hashmap
    buckets: [*]const Bucket,
    /// Metadata of the hashmap
    meta: [*]const u8,
    /// key+value strings concatenated together
    data: [*]const u8,
    /// Capacity of the hashmap
    cap: Size,
    /// The current index
    i: Size = 0,

    pub fn next(it: *Iterator) ?KV {
      if (it.i >= it.cap) return null;
      while (it.i < it.cap) {
        defer it.i += 1;
        if (it.meta[0..it.cap][it.i] == 0) continue;
        const bucket = it.buckets[0..it.cap][it.i];
        const next_bucket = it.buckets[0..it.cap][it.i + 1];
        return .{
          .key = it.data[@intCast(bucket.key_idx)..][0..@intCast(bucket.key_len)],
          .value = it.data[0..@intCast(next_bucket.key_idx)][@intCast(bucket.key_idx)..][@intCast(bucket.key_len)..]
        };
      }
      return null;
    }
  };

  pub fn iterator(self: *const @This()) Iterator {
    return .{ .buckets = self.buckets().ptr, .meta = self.meta().ptr, .data = self.data().ptr, .cap = self.cap };
  }
  pub inline fn data(self: *const @This()) []const u8 { return self._meta[self.cap..][0..self._data_size]; }
  pub inline fn count(self: *const @This()) usize { return self.size; }
  pub inline fn capacity(self: *const @This()) usize { return self.cap; }
  pub inline fn buckets(self: *const @This()) []const Bucket {
    return @as([*]const Bucket, @ptrCast(@alignCast((self._meta - @as(usize, (self.cap + 1) * @sizeOf(Bucket))))))[0..self.cap+1];
  }
  pub inline fn meta(self: *const @This()) []const u8 { return self._meta[0..self.cap]; }

  pub fn get(self: *const @This(), key: []const u8) ?[]const u8 {
    const hash, const fingerprint = HashMap.getHFP(key);
    var i: usize = @intCast(hash & (self.cap - 1));
    const buckets_v = self.buckets();
    const data_v = self.data();
    while (self.meta()[i] != 0) : (i = (i + 1) & (self.cap - 1)) {
      const bucket = buckets_v[i];
      if (self.meta()[i] == fingerprint and std.mem.eql(u8, key, data_v[@intCast(bucket.key_idx)..][0..@intCast(bucket.key_len)])) {
        const next = buckets_v[i + 1];
        return data_v[0..@intCast(next.key_idx)][@intCast(bucket.key_idx)..][@intCast(bucket.key_len)..];
      }
    }

    return null;
  }

  /// Release the backing memory and invalidate this map.
  pub fn deinit(self: *@This(), allocator: std.mem.Allocator) void {
    const buckets_ptr = @as([*]align(@alignOf(Bucket)) u8, @ptrCast(@constCast(self.buckets().ptr)));
    const allocation_size = (self.cap + 1) * @sizeOf(Bucket) + self.cap + self._data_size;
    allocator.free(buckets_ptr[0..allocation_size]);
    self._meta = undefined;
    self._data_size = undefined;
  }
};

/// Not sure if this is that good of an idea
fn isOneOf(c: u8, comptime chars: []const u8) bool {
  const VectorType = @Vector(chars.len, u8);
  const query_vec: VectorType = chars[0..chars.len].*;
  const current_vec: VectorType = @splat(c);
  return @reduce(.Min, query_vec ^ current_vec) == 0;
}

/// Escape a character, otherwise return null
/// we return a pointer so that it is trivially convertible to a string slice
/// we can do this as the string literals are statically stored in the binary
fn escaped(c: u8) ?*const [2]u8 {
  return switch (c) {
    '\\' => "\\\\",
    '\n' => "\\n",
    '\r' => "\\r",
    '\t' => "\\t",
    '\x0B' => "\\v",
    '\x0C' => "\\f",
    inline else => null,
  };
}

/// Mapping for decoding hex characters
const HEX_DECODE_ARRAY = blk: {
  var all: ['f' - '0' + 1]u8 = undefined;
  for ('0'..('9' + 1)) |b| all[b - '0'] = b - '0';
  for ('A'..('F' + 1)) |b| all[b - '0'] = b - 'A' + 10;
  for ('a'..('f' + 1)) |b| all[b - '0'] = b - 'a' + 10;
  break :blk all;
};

inline fn decodeHex(char: u8) u8 {
  return HEX_DECODE_ARRAY[char - @as(usize, '0')];
}

pub fn GetParser(options: ParseOptions) type {
  return struct {
    map: HashMap,
    at: usize = 0,
    line: usize = 0,
    line_start: usize = 0,

    /// Returns true if the whole string has been parsed
    fn done(self: *@This()) bool {
      return self.at >= self.map.keys_string.len;
    }

    /// Returns the current character
    fn current(self: *@This()) ?u8 {
      if (self.done()) return null;
      return self.map.keys_string[self.at];
    }

    /// Returns the current character, assert that it exists
    fn last(self: *@This()) u8 {
      std.debug.assert(self.at != 0);
      return self.map.keys_string[self.at - 1];
    }

    /// Returns the current character and advances the pointer
    fn take(self: *@This()) ?u8 {
      if (self.done()) return null;
      self.at += 1;
      return self.last();
    }

    /// Returns the current character (as u9) and advances the pointer
    fn takeU9(self: *@This()) u9 {
      return self.take() orelse 0x100;
    }

    /// Skips all characters until the given character is found
    fn skipUpto(self: *@This(), comptime end: u8) void {
      self.skipUptoAny(std.fmt.comptimePrint("{c}", .{end}));
    }

    /// Skips all characters until any of the given characters is found
    fn skipUptoAny(self: *@This(), comptime end: []const u8) void {
      while (self.at < self.map.keys_string.len and !isOneOf(self.current().?, end)) {
        self.at += 1;
      }
    }

    /// Skips all characters that belong to the given chars set
    fn skipAny(self: *@This(), comptime chars: []const u8) void {
      while (self.at < self.map.keys_string.len and isOneOf(self.current().?, chars)) {
        self.at += 1;
      }
    }

    /// Returns the current character as a slice (for printing)
    fn currentAsSlice(self: *@This()) []const u8 {
      std.debug.assert(self.at < self.map.keys_string.len);
      return self.map.keys_string[self.at..][0..1];
    }

    /// Prints the error marker at the current position
    fn printErrorMarker(self: *@This()) void {
      const at = self.at;
      self.map.keys_string = self.map.keys_string[0.. @min(self.at + options.max_error_line_peek, self.map.keys_string.len)];
      self.skipUpto('\n');
      options.log_fn(":{d}:{d}\n{s}\n", .{self.line, at - self.line_start, self.map.keys_string[self.line_start..self.at]});
      if (@inComptime()) {
        options.log_fn((" " ** @as(usize, at - self.line_start - 1)) ++ "^\n", .{});
      } else {
        for (1..at - self.line_start) |_| {
          options.log_fn(" ", .{});
        }
        options.log_fn("^\n", .{});
      }
    }

    /// Parses the key
    fn parseKey(self: *@This()) ParseKeyError!?HashMap.String {
      // Skip any whitespace / comment lines, break at first non-whitespace character
      while (true) {
        self.skipAny(" \t\x0B\r\x0C");
        const c = self.current() orelse return null;

        if (c == '#') {
          self.skipUpto('\n');
          _ = self.take();
        } else if (c == '\n') {
          self.line += 1;
          self.line_start = self.at;
          _ = self.take();
        } else break;
      }

      const start = self.at; // starting index of our key in the string

      // ensure first key char is valid
      if (!options.is_valid_first_key_char(self.take().?)) {
        self.at -= 1;
        options.log_fn("Invalid first character `{s}` for key at ", .{escaped(self.current().?) orelse self.currentAsSlice()});
        self.printErrorMarker();
        return ParseKeyError.InvalidFirstKeyChar;
      }

      // Consume key chars untile we encounter something unexpected
      while (self.current()) |c| {
        if (isOneOf(c, " \t\x0B=")) { // The key is done
          break;
        } else if (!options.is_valid_key_char(c)) { // Parse the key character
          options.log_fn("Invalid character `{s}` while parsing key at ", .{escaped(c) orelse self.currentAsSlice()});
          self.printErrorMarker();
          return ParseKeyError.InvalidKeyChar;
        }
        self.at += 1;
      } else {
        options.log_fn("Unexpected end of file while parsing key at ", .{});
        self.at = start;
        self.printErrorMarker();

        return ParseKeyError.UnexpectedEndOfFile;
      }

      // Index and length of the key inside the provided data (self.map.keys_string)
      const retval: HashMap.String = .{ .idx = @intCast(start), .len = @intCast(self.at - start) };

      // consume whitespace, then the = character
      self.skipAny(" \t\x0B");
      const end_char = self.take() orelse {
        options.log_fn("Unexpected end of file, expected `=` ", .{});
        self.printErrorMarker();
        return ParseKeyError.UnexpectedEndOfFile;
      };

      // There must be an = character. orelse we return an error
      if (end_char == '=') return retval;

      options.log_fn("Got unexpected `{s}`, expected `=` ", .{escaped(end_char) orelse self.currentAsSlice()});
      self.printErrorMarker();
      return ParseKeyError.InvalidKeyChar;
    }

    fn parseValue(self: *@This()) ParseValueError!void {
      self.skipAny(" \t\x0B"); // skip any preceding whitespace
      if (self.current()) |c| {
        return switch (c) { // check if the value is quoted or unquoted
          '\'' => self.parseQuotedValue('\''),
          '"' => self.parseQuotedValue('"'),
          '#' => {
            self.skipUpto('\n');
            _ = self.take();
            return;
          },
          else => self.parseQuotedValue(null),
        };
      } else return;
    }

    /// This function is called when out value is quted and we wanna remove the trailing whitespace
    fn trimResultEnd(self: *@This()) void {
      while (self.map.values_string.items.len > 0 and isOneOf(self.map.values_string.items[self.map.values_string.items.len - 1], " \t\x0B\r\x0C")) {
        self.map.values_string.items.len -= 1;
      }
    }

    /// Unlike how the name suggests, this parses the unquoted value as well when quote_char is null
    fn parseQuotedValue(self: *@This(), comptime quote_char: ?u8) ParseValueError!void {
      if (quote_char) |qc| std.debug.assert(qc == self.take().?);

      // This is used for logging only
      const quote_string = if (quote_char) |c| comptime std.fmt.comptimePrint(" quoted({c})", .{c}) else "";

      // We use a switch block and not a while loop (cuz we don't need a while loop!)
      // Keeps our code clean i think
      // Since zig can't switch on ?u8, we convert it to a u9 and set it's value to 0x100 if it's null
      // we then switch on the u9 to get effectively the same thing
      blk: switch (self.takeU9()) {
        0x100 => { // the data has been exhausted
          // we can just return the value in unquoted case
          if (quote_char == null) break :blk;

          // The quote was not closed, hence we return an error.
          // We know this because on closing the quote, the switch block is exited and
          // we could not have ended up here
          options.log_fn("Unexpected end of file while parsing a{s} value at ", .{quote_string});
          self.printErrorMarker();
          return ParseValueError.UnterminatedQuote;
        },
        '\\' => { // Special logic for when we see a backslash
          switch (if (quote_char) |c| @as(u9, c) else 0x100) { // switch on the quote_char
            0x100 => switch (self.takeU9()) {
              0x100 => continue :blk 0x100,
              '\\', '$' => |c| try self.map.values_string.append(self.map.allocator, @intCast(c)),
              '\n' => {
                self.line += 1;
                self.line_start = self.at;
                try self.map.values_string.append(self.map.allocator, '\n');
              },
              else => |c| try self.map.values_string.appendSlice(self.map.allocator, &[_]u8{'\\', @intCast(c)}),
            },
            '\'' => switch (self.takeU9()) {
              0x100 => continue :blk 0x100,
              '\\', '\'' => |c| try self.map.values_string.append(self.map.allocator, @intCast(c)),
              '\n' => {
                self.line += 1;
                self.line_start = self.at;
                try self.map.values_string.append(self.map.allocator, '\n');
              },
              else => |c| try self.map.values_string.appendSlice(self.map.allocator, &[_]u8{'\\', @intCast(c)}),
            },
            '"' => switch (self.takeU9()) {
              0x100 => continue :blk 0x100,
              '\\' => try self.map.values_string.append(self.map.allocator, '\\'),
              'n' => try self.map.values_string.append(self.map.allocator, '\n'),
              'r' => try self.map.values_string.append(self.map.allocator, '\r'),
              't' => try self.map.values_string.append(self.map.allocator, '\t'),
              'v' => try self.map.values_string.append(self.map.allocator, '\x0B'),
              'f' => try self.map.values_string.append(self.map.allocator, '\x0C'),
              'x' => {
                const hexa = self.take() orelse continue :blk 0x100;
                const hexb = self.take() orelse continue :blk 0x100;
                if (!std.ascii.isHex(hexa) or !std.ascii.isHex(hexb)) {
                  options.log_fn("Invalid hex escape sequence `\\x{s}{s}` in a{s} value at ", .{
                    escaped(hexa) orelse self.map.keys_string[self.at - 2..][0..1],
                    escaped(hexb) orelse self.map.keys_string[self.at - 1..][0..1],
                    quote_string,
                  });
                  self.at -= if (!std.ascii.isHex(hexa)) 2 else 1;
                  self.printErrorMarker();
                  return ParseValueError.InvalidEscapeSequence;
                }

                try self.map.values_string.append(self.map.allocator, @intCast((decodeHex(hexa) << 4) | decodeHex(hexb)));
              },
              inline '$', '\"' => |c| try self.map.values_string.append(self.map.allocator, c),
              else => |c_u9| { // This is Always and error since double quotes require proper escaping
                options.log_fn("Unexpected escape sequence `\\{s}` in a{s} value at ", .{
                  escaped(@intCast(c_u9)) orelse self.currentAsSlice(), quote_string
                });
                self.at -= 1;
                self.printErrorMarker();
                return ParseValueError.InvalidEscapeSequence;
              }
            },
            else => unreachable,
          }
          continue :blk self.takeU9();
        },
        '$' => { // Try to parse the ${...} block
          const next = self.takeU9();
          if (quote_char == '\'' or next != '{') {
            try self.map.values_string.append(self.map.allocator, '$');
            continue :blk next;
          }

          const start = self.at; // Start of the key, we don't strip whitespace in the block
          if (!options.is_valid_first_key_char(self.take() orelse {
            options.log_fn("Unexpected end of file while parsing {{}} in a{s} value at ", .{quote_string});
            self.printErrorMarker();
            return ParseValueError.UnterminatedSubstitutionBlock;
          })) {
            self.at -= 1;
            options.log_fn("Invalid first character `{s}` for key at ", .{escaped(self.current().?) orelse self.currentAsSlice()});
            self.printErrorMarker();
            return ParseKeyError.InvalidFirstKeyChar;
          }

          while (self.current()) |c| {
            if (c == '}') {
              self.at += 1;
              break;
            }
            if (!options.is_valid_key_char(c)) {
              options.log_fn("Invalid character `{c}` while parsing key at ", .{c});
              self.printErrorMarker();
              return ParseKeyError.InvalidKeyChar;
            }
            self.at += 1;
          } else {
            options.log_fn("Unexpected end of file while parsing key for {{}} in a{s} value at ", .{quote_string});
            self.printErrorMarker();
            return ParseValueError.UnterminatedSubstitutionBlock;
          }

          const key = self.map.keys_string[start..self.at - 1];
          const maybe_val = self.map.get(key);
          const val = maybe_val orelse {
            options.log_fn("Substitution key `{s}` not found in map; at ", .{key});
            self.at = start;
            self.printErrorMarker();
            return ParseValueError.SubstitutionKeyNotFound;
          };

          try self.map.values_string.appendSlice(self.map.allocator, val);
          continue :blk self.takeU9();
        },
        '\n' => {
          self.line += 1;
          self.line_start = self.at;
          if (quote_char == null) {
            self.trimResultEnd();
            return;
          }
          try self.map.values_string.append(self.map.allocator, '\n');
          continue :blk self.takeU9();
        },
        else => |c_9| { // default case
          const c: u8 = @intCast(c_9);
          if (quote_char) |qc| {
            if (c == qc) break :blk;
          } else if (c == '#') {
            self.skipUpto('\n');
            self.trimResultEnd();
            return;
          }
          if (quote_char != null and c == quote_char.?) break :blk;

          try self.map.values_string.append(self.map.allocator, c);
          continue :blk self.takeU9();
        },
      }

      if (quote_char == null) self.trimResultEnd();
      self.skipAny(" \t\x0B\r\x0C");
      const c = self.take() orelse return;
      if (c == '\n') return;
      if (c != '#') {
        options.log_fn("Unexpected character `{c}` in a{s} value at ", .{c, quote_string});
        self.printErrorMarker();
        return ParseValueError.UnexpectedCharacter;
      }

      self.skipUpto('\n');
      _ = self.take();
    }

    /// Combined parsing function for both runtime and comptime
    fn parse(data: []const u8, allocator: std.mem.Allocator) ParseValueError!HashMap {
      @setEvalBranchQuota(1000_000);
      var self: @This() = .{ .map = try .init(data, 32, allocator) };
      errdefer self.map.deinit();

      while (try self.parseKey()) |key| {
        const value_idx = self.map.values_string.items.len;
        try self.parseValue();
        try self.map.put(key, .{ .idx = value_idx, .len = self.map.values_string.items.len - value_idx });
      }

      return self.map;
    }
  };
}

//------
// Tests
//------

test {
  std.testing.refAllDeclsRecursive(@This());
}

const ENV_TEST_STRING_1: []const u8 = 
  \\ # This is a comment
  \\NOTHING=# This is also a comment so NOTHING should be an empty string
  \\NOTHING = "" # You can override values, this is still an empty string
  \\HOSTNAME = localhost
  \\PORT = 8080
  \\URL = http://${HOSTNAME}:${PORT}
  \\FALLBACK = "${NOTHING}"
  \\LITERAL = '${This Will Not Be Substitutes}'
  \\ESCAPE_SEQUENCES = "\xff\n\r\v\f"
  \\# 5 = 6 #this will cause an error if uncommented
  \\MULTILINE_VALUE = "Multi
  \\line
  \\    value"
  \\UNQUOTED_MULTILINE = Multi\
  \\line\
  \\    value # comments are allowed here but not after the `\`
;

test loadFrom {
  var parsed = try loadFromData(ENV_TEST_STRING_1, std.testing.allocator, .{});
  defer parsed.deinit(std.testing.allocator);

  // var iter = parsed.iterator();
  // while (iter.next()) |kv| {
  //   std.debug.print("`{s}`: `{s}`\n", .{ENV_TEST_STRING_1[kv.key_ptr.*.idx..][0..kv.key_ptr.*.len], kv.value_ptr.*});
  // }

  try std.testing.expectEqualStrings("", parsed.get("NOTHING").?);
  try std.testing.expectEqualStrings("localhost", parsed.get("HOSTNAME").?);
  try std.testing.expectEqualStrings("8080", parsed.get("PORT").?);
  try std.testing.expectEqualStrings("http://localhost:8080", parsed.get("URL").?);
  try std.testing.expectEqualStrings("", parsed.get("FALLBACK").?);
  try std.testing.expectEqualStrings("${This Will Not Be Substitutes}", parsed.get("LITERAL").?);
  try std.testing.expectEqualStrings("\xff\n\r\x0B\x0C", parsed.get("ESCAPE_SEQUENCES").?);
  try std.testing.expectEqualStrings("Multi\nline\n    value", parsed.get("MULTILINE_VALUE").?);
  try std.testing.expectEqualStrings("Multi\nline\n    value", parsed.get("UNQUOTED_MULTILINE").?);

  const TestFns = struct {
    fn loadFn(comptime data: []const u8, comptime options: ParseOptions) ParseError!EnvType {
      return loadFromData(data, std.testing.allocator, options);
    }

    fn deinitFn(v: *EnvType) void {
      v.deinit(std.testing.allocator);
    }
  };

  const tests = GetTests(TestFns.loadFn, TestFns.deinitFn);
  runTests(false, tests);
}

test loadFromComptime {
  const parsed = comptime loadFromDataComptime(ENV_TEST_STRING_1, .{})  catch |e| @compileError(@errorName(e));

  // var iter = parsed.iterator();
  // while (iter.next()) |kv| {
  //   std.debug.print("`{s}`: `{s}`\n", .{kv.key, kv.value});
  // }

  try std.testing.expectEqualStrings("", parsed.get("NOTHING").?);
  try std.testing.expectEqualStrings("localhost", parsed.get("HOSTNAME").?);
  try std.testing.expectEqualStrings("8080", parsed.get("PORT").?);
  try std.testing.expectEqualStrings("http://localhost:8080", parsed.get("URL").?);
  try std.testing.expectEqualStrings("", parsed.get("FALLBACK").?);
  try std.testing.expectEqualStrings("${This Will Not Be Substitutes}", parsed.get("LITERAL").?);
  try std.testing.expectEqualStrings("\xff\n\r\x0B\x0C", parsed.get("ESCAPE_SEQUENCES").?);
  try std.testing.expectEqualStrings("Multi\nline\n    value", parsed.get("MULTILINE_VALUE").?);
  try std.testing.expectEqualStrings("Multi\nline\n    value", parsed.get("UNQUOTED_MULTILINE").?);

  const tests = comptime GetTests(loadFromDataComptime, struct {
    fn deinitFn(_: *ComptimeEnvType) void {}
  }.deinitFn);
  comptime runTests(true, tests);
}

fn runTests(comptime in_comptime: bool, comptime T: type) void {
  inline for (@typeInfo(T).@"struct".decls) |f| {
    _ = struct {
      test {
        if (!in_comptime) {
          @field(T, f.name)() catch |e| {
            std.debug.print("TEST FAILED: {s}\n", .{f.name});
            return e;
          };
        } else {
          comptime {
            @field(T, f.name)() catch |e| {
              @compileError(std.fmt.comptimePrint("TEST \"{s}\": {any}\n", .{f.name, e}));
            };
          }
        }
      }
    };
  }
}

fn GetTests(loadFn: anytype, deinitFn: anytype) type {
  return struct {
    pub fn @"invalid first key character"() !void {
      const test_data =
        \\ 1KEY=value
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidFirstKeyChar, err);
    }

    pub fn @"invalid key character"() !void {
      const test_data =
        \\ KEY!=value
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidKeyChar, err);
    }

    pub fn @"unterminated double quote"() !void {
      const test_data =
        \\ KEY="unterminated value
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.UnterminatedQuote, err);
    }

    pub fn @"unterminated single quote"() !void {
      const test_data =
        \\ KEY='unterminated value
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.UnterminatedQuote, err);
    }

    pub fn @"invalid escape sequence in double quotes"() !void {
      const test_data =
        \\ KEY="val\zue"
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidEscapeSequence, err);
    }

    pub fn @"invalid hex escape in double quotes"() !void {
      const test_data =
        \\ KEY="val\xg12"
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidEscapeSequence, err);
    }

    pub fn @"valid hex escape in double quotes"() !void {
      const test_data =
        \\ KEY="val\xFFue"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val\xFFue", parsed.get("KEY").?);
    }

    pub fn @"substitution key not found"() !void {
      const test_data =
        \\ KEY=${MISSING}
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.SubstitutionKeyNotFound, err);
    }

    pub fn @"substitution in single quotes does not expand"() !void {
      const test_data =
        \\ HOST=world
        \\ KEY='${HOST}'
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("${HOST}", parsed.get("KEY").?);
    }

    pub fn @"substitution outside double quotes"() !void {
      const test_data =
        \\ HOST=world
        \\ KEY=unquoted${HOST}
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("unquotedworld", parsed.get("KEY").?);
    }

    pub fn @"empty file"() !void {
      const test_data = "";
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqual(@as(usize, 0), parsed.count());
    }

    pub fn @"only comments"() !void {
      const test_data =
        \\ # Comment line 1
        \\# Comment line 2
        \\  # Comment with spaces
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqual(@as(usize, 0), parsed.count());
    }

    pub fn @"inline comment trims trailing space"() !void {
      const test_data =
        \\ KEY=val # comment
        \\ KEY2=val2   # comment with spaces
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val", parsed.get("KEY").?);
      try std.testing.expectEqualStrings("val2", parsed.get("KEY2").?);
    }

    pub fn @"unquoted value trims leading and trailing spaces"() !void {
      const test_data =
        \\ KEY= val 
        \\ KEY2 =  va l  
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val", parsed.get("KEY").?);
      try std.testing.expectEqualStrings("va l", parsed.get("KEY2").?);
    }

    pub fn @"unquoted value preserves interior spaces"() !void {
      const test_data =
        \\ KEY=va l
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va l", parsed.get("KEY").?);
    }

    pub fn @"single quotes preserve escapes literally"() !void {
      const test_data =
        \\ KEY='va\nl'
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va\\nl", parsed.get("KEY").?);
    }

    pub fn @"double quotes expand newline escape"() !void {
      const test_data =
        \\ KEY="va\nl"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      const expected = "va" ++ &[_]u8{'\n'} ++ "l";
      try std.testing.expectEqualStrings(expected, parsed.get("KEY").?);
    }

    pub fn @"double quotes handle backslash escape"() !void {
      const test_data =
        \\ KEY="va\\nl"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va\\nl", parsed.get("KEY").?);
    }

    pub fn @"double quotes handle quote escape"() !void {
      const test_data =
        \\ KEY="va\"nl"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va\"nl", parsed.get("KEY").?);
    }

    pub fn @"multiline literal in double quotes"() !void {
      const test_data =
        \\ KEY="Multi
        \\line
        \\  value"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      const expected = "Multi\nline\n  value";
      try std.testing.expectEqualStrings(expected, parsed.get("KEY").?);
    }

    pub fn @"export prefix not handled (parses as invalid key)"() !void {
      const test_data =
        \\ export KEY=value
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidKeyChar, err);
    }

    pub fn @"unexpected end of file in key"() !void {
      const test_data =
        \\ KEY
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.UnexpectedEndOfFile, err);
    }

    pub fn @"unexpected character after key"() !void {
      const test_data =
        \\ KEY? = value
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidKeyChar, err);
    }

    pub fn @"duplicate keys overwrite with last value"() !void {
      const test_data =
        \\ KEY=first
        \\ KEY=second
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("second", parsed.get("KEY").?);
    }

    pub fn @"windows line endings are handled"() !void {
      const test_data = "KEY=value\r\nKEY2= value2 \r\n";
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("value", parsed.get("KEY").?);
      try std.testing.expectEqualStrings("value2", parsed.get("KEY2").?);
    }

    pub fn @"double quotes expand carriage return escape"() !void {
      const test_data =
        \\ KEY="va\rl"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      const expected = "va" ++ &[_]u8{'\r'} ++ "l";
      try std.testing.expectEqualStrings(expected, parsed.get("KEY").?);
    }

    pub fn @"double quotes expand tab escape"() !void {
      const test_data =
        \\ KEY="va\tl"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      const expected = "va" ++ &[_]u8{'\t'} ++ "l";
      try std.testing.expectEqualStrings(expected, parsed.get("KEY").?);
    }

    pub fn @"double quotes expand vertical tab escape"() !void {
      const test_data =
        \\ KEY="va\vl"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      const expected = "va" ++ &[_]u8{'\x0B'} ++ "l";
      try std.testing.expectEqualStrings(expected, parsed.get("KEY").?);
    }

    pub fn @"double quotes expand form feed escape"() !void {
      const test_data =
        \\ KEY="va\fl"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      const expected = "va" ++ &[_]u8{'\x0C'} ++ "l";
      try std.testing.expectEqualStrings(expected, parsed.get("KEY").?);
    }

    pub fn @"unterminated substitution block"() !void {
      const test_data =
        \\ KEY=${UNTERMINATED
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.UnterminatedSubstitutionBlock, err);
    }

    pub fn @"substitution key with invalid character"() !void {
      const test_data =
        \\ KEY=valid
        \\ URL=http://${KEY}${KEY!}
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidKeyChar, err);
    }

    pub fn @"empty substitution key"() !void {
      const test_data =
        \\ KEY=${}
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidFirstKeyChar, err);
    }

    pub fn @"value ends with newline in unquoted"() !void {
      const test_data = 
        \\KEY=value\n
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("value\\n", parsed.get("KEY").?);
    }

    pub fn @"inline comment without space is parsed"() !void {
      const test_data =
        \\ KEY=val#comment
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val", parsed.get("KEY").?);
    }

    pub fn @"quoted values preserve trailing spaces"() !void {
      const test_data =
        \\ KEY="val "
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val ", parsed.get("KEY").?);
    }

    pub fn @"single quotes handle escaped single quote"() !void {
      const test_data =
        \\ KEY='va\'l'
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va'l", parsed.get("KEY").?);
    }

    pub fn @"double quotes handle hex escape with lowercase"() !void {
      const test_data =
        \\ KEY="val\xffue"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val\xFFue", parsed.get("KEY").?);
    }

    pub fn @"single quotes does not parse hex char"() !void {
      const test_data =
        \\ KEY='val\xg12'
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val\\xg12", parsed.get("KEY").?);
    }

    pub fn @"double quotes escaped dollar"() !void {
      const test_data =
        \\ KEY="va\${l}"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va${l}", parsed.get("KEY").?);
    }

    pub fn @"substitution in multiline double quotes"() !void {
      const test_data =
        \\ HOST=world
        \\ KEY="Multi
        \\${HOST}
        \\line"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      const expected = "Multi\nworld\nline";
      try std.testing.expectEqualStrings(expected, parsed.get("KEY").?);
    }

    pub fn @"whitespace only lines are skipped"() !void {
      const test_data = "   \t \nKEY=value";
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("value", parsed.get("KEY").?);
    }

    pub fn @"unquoted value with tab trims"() !void {
      const test_data = "KEY=\tval\t";
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val", parsed.get("KEY").?);
    }

    pub fn @"quoted value with interior tab preserved"() !void {
      const test_data = "KEY=\"va\tl\"";
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      const expected = "va\tl";
      try std.testing.expectEqualStrings(expected, parsed.get("KEY").?);
    }

    pub fn @"trailing newline in file"() !void {
      const test_data = "KEY=value\n";
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("value", parsed.get("KEY").?);
    }

    pub fn @"key starting with underscore"() !void {
      const test_data =
        \\ _KEY=value
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("value", parsed.get("_KEY").?);
    }

    pub fn @"value with only whitespace trims to empty"() !void {
      const test_data = "KEY=   \t";
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("", parsed.get("KEY").?);
    }

    pub fn @"partial hex escape errors"() !void {
      const test_data =
        \\ KEY="val\xG"
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.InvalidEscapeSequence, err);
    }

    pub fn @"escaped newline in single quotes literal"() !void {
      const test_data =
        \\ KEY='va\nl'
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va\\nl", parsed.get("KEY").?);
    }

    pub fn @"substitution key with digits"() !void {
      const test_data =
        \\ KEY123=val
        \\ URL=${KEY123}
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val", parsed.get("URL").?);
    }

    pub fn @"inline comment after quoted value"() !void {
      const test_data =
        \\ KEY="val" # comment
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val", parsed.get("KEY").?);
    }

    pub fn @"key with multiple = parses first"() !void {
      const test_data =
        \\ KEY=val=more
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val=more", parsed.get("KEY").?);
    }

    pub fn @"escaped quote inside single quotes"() !void {
      const test_data =
        \\ KEY='va\'\'l'
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va''l", parsed.get("KEY").?);
    }

    pub fn @"unquoted value ending with backslash literal"() !void {
      const test_data =
        \\ KEY=val\\
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val\\", parsed.get("KEY").?);
    }

    pub fn @"substitution EOF in key"() !void {
      const test_data =
        \\ KEY=${UNFINISHED
      ;
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.UnterminatedSubstitutionBlock, err);
    }

    pub fn @"no value after ="() !void {
      const test_data =
        \\ KEY=
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("", parsed.get("KEY").?);
    }

    pub fn @"comment after whitespace"() !void {
      const test_data =
        \\ KEY=value   # comment
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("value", parsed.get("KEY").?);
    }

    pub fn @"quoted value with leading space preserved"() !void {
      const test_data =
        \\ KEY=" val "
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings(" val ", parsed.get("KEY").?);
    }

    pub fn @"single quotes with backslash literal"() !void {
      const test_data =
        \\ KEY='va\\l'
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("va\\l", parsed.get("KEY").?);
    }

    pub fn @"hex escape at end of value"() !void {
      const test_data =
        \\ KEY="val\xFF"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("val\xFF", parsed.get("KEY").?);
    }

    pub fn @"unexpected characters after quoted value"() !void {
      const test_data = "KEY=\"value\" extra";
      const err = loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      try std.testing.expectError(ParseValueError.UnexpectedCharacter, err);
    }

    pub fn @"unquoted value with accented characters"() !void {
      const test_data =
        \\ KEY=café
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("café", parsed.get("KEY").?);
    }

    pub fn @"double quoted value with emoji"() !void {
      const test_data =
        \\ KEY="Hello 😊 World"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("Hello 😊 World", parsed.get("KEY").?);
    }

    pub fn @"single quoted value with Chinese characters"() !void {
      const test_data =
        \\ KEY='你好世界'
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("你好世界", parsed.get("KEY").?);
    }

    pub fn @"unquoted value with Cyrillic"() !void {
      const test_data =
        \\ KEY=Привет
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("Привет", parsed.get("KEY").?);
    }

    pub fn @"double quoted value with Arabic"() !void {
      const test_data =
        \\ KEY="مرحبا بالعالم"
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("مرحبا بالعالم", parsed.get("KEY").?);
    }

    pub fn @"unquoted value with mixed UTF-8 and ASCII, interior em space"() !void {
      const test_data =
        \\ KEY=café world  # em space interior
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("café world", parsed.get("KEY").?);
    }

    pub fn @"substitution expands to UTF-8 value"() !void {
      const test_data =
        \\ GREETING=Hola
        \\ PLACE=México
        \\ MSG=${GREETING} desde ${PLACE}!
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("Hola desde México!", parsed.get("MSG").?);
    }

    pub fn @"double quoted value with trailing zero-width space trimmed"() !void {
      const test_data =
        \\ KEY="test"  # zero-width space
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("test", parsed.get("KEY").?);
    }

    pub fn @"unquoted value with Japanese"() !void {
      const test_data =
        \\ KEY=こんにちは
      ;
      var parsed = try loadFn(test_data, .{ .log_fn = ParseOptions.NopLogFn });
      defer deinitFn(&parsed);
      try std.testing.expectEqualStrings("こんにちは", parsed.get("KEY").?);
    }
  };
}

