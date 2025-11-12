//! copyv: track https://github.com/ziglang/zig/blob/cbfa87cbea0274e1e88d6a61bba82a2099e19fd6/lib/std/hash_map.zig#L1-L2143
//! This file contains a fork of the Zig stdlib HashMap implementation tuned
//! for use with our terminal page representation.
//!
//! The main goal we need to achieve that wasn't possible with the stdlib
//! HashMap is to utilize offsets rather than full pointers so that we can
//! copy around the entire backing memory and keep the hash map working.
//!
//! Additionally, for serialization/deserialization purposes, we need to be
//! able to create a HashMap instance and manually set the offsets up. The
//! stdlib HashMap does not export Metadata so this isn't possible.
//!
//! Also, I want to be able to understand possible capacity for a given K,V
//! type and fixed memory amount. The stdlib HashMap doesn't publish its
//! internal allocation size calculation.
//!
//! Finally, I removed many of the APIs that we'll never require for our
//! usage just so that this file is smaller, easier to understand, and has
//! less opportunity for bugs.
//!
//! Besides these shortcomings, the stdlib HashMap has some great qualities
//! that we want to keep, namely the fact that it is backed by a single large
//! allocation rather than pointers to separate allocations. This is important
//! because our terminal page representation is backed by a single large
//! allocation so we can give the HashMap a slice of memory to operate in.
//!
//! I haven't carefully benchmarked this implementation against other hash
//! map implementations. It's possible using some of the newer variants out
//! there would be better. However, I trust the built-in version is pretty good
//! and its more important to get the terminal page representation working
//! first then we can measure and improve this later if we find it to be a
//! bottleneck.

const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;
const autoHash = std.hash.autoHash;
const math = std.math;
const mem = std.mem;
const Allocator = mem.Allocator;
const Wyhash = std.hash.Wyhash;
const Alignment = std.mem.Alignment;

<<<<<<< ours
const Offset = @import("size.zig").Offset;
const OffsetBuf = @import("size.zig").OffsetBuf;
const getOffset = @import("size.zig").getOffset;
||||||| base
pub fn getAutoHashFn(comptime K: type, comptime Context: type) (fn (Context, K) u64) {
    comptime {
        assert(@hasDecl(std, "StringHashMap")); // detect when the following message needs updated
        if (K == []const u8) {
            @compileError("std.auto_hash.autoHash does not allow slices here (" ++
                @typeName(K) ++
                ") because the intent is unclear. " ++
                "Consider using std.StringHashMap for hashing the contents of []const u8. " ++
                "Alternatively, consider using std.auto_hash.hash or providing your own hash function instead.");
        }
    }

    return struct {
        fn hash(ctx: Context, key: K) u64 {
            _ = ctx;
            if (std.meta.hasUniqueRepresentation(K)) {
                return Wyhash.hash(0, std.mem.asBytes(&key));
            } else {
                var hasher = Wyhash.init(0);
                autoHash(&hasher, key);
                return hasher.final();
            }
        }
    }.hash;
}

pub fn getAutoEqlFn(comptime K: type, comptime Context: type) (fn (Context, K, K) bool) {
    return struct {
        fn eql(ctx: Context, a: K, b: K) bool {
            _ = ctx;
            return std.meta.eql(a, b);
        }
    }.eql;
}
=======
pub fn getAutoHashFn(comptime K: type, comptime Context: type) (fn (Context, K) u64) {
    comptime {
        assert(@hasDecl(std, "StringHashMap")); // detect when the following message needs updated
        if (K == []const u8) {
            @compileError("std.hash.autoHash does not allow slices here (" ++
                @typeName(K) ++
                ") because the intent is unclear. " ++
                "Consider using std.StringHashMap for hashing the contents of []const u8. " ++
                "Alternatively, consider using std.hash.autoHashStrat or providing your own hash function instead.");
        }
    }

    return struct {
        fn hash(ctx: Context, key: K) u64 {
            _ = ctx;
            if (std.meta.hasUniqueRepresentation(K)) {
                return Wyhash.hash(0, std.mem.asBytes(&key));
            } else {
                var hasher = Wyhash.init(0);
                autoHash(&hasher, key);
                return hasher.final();
            }
        }
    }.hash;
}

pub fn getAutoEqlFn(comptime K: type, comptime Context: type) (fn (Context, K, K) bool) {
    return struct {
        fn eql(ctx: Context, a: K, b: K) bool {
            _ = ctx;
            return std.meta.eql(a, b);
        }
    }.eql;
}
>>>>>>> theirs

pub fn AutoOffsetHashMap(comptime K: type, comptime V: type) type {
    return OffsetHashMap(K, V, AutoContext(K));
}

fn AutoHashMapUnmanaged(comptime K: type, comptime V: type) type {
    return HashMapUnmanaged(K, V, AutoContext(K));
}

fn AutoContext(comptime K: type) type {
    return struct {
        pub const hash = std.hash_map.getAutoHashFn(K, @This());
        pub const eql = std.hash_map.getAutoEqlFn(K, @This());
    };
}

<<<<<<< ours
/// A HashMap type that uses offsets rather than pointers, making it
/// possible to efficiently move around the backing memory without
/// invalidating the HashMap.
pub fn OffsetHashMap(
||||||| base
/// Builtin hashmap for strings as keys.
/// Key memory is managed by the caller.  Keys and values
/// will not automatically be freed.
pub fn StringHashMap(comptime V: type) type {
    return HashMap([]const u8, V, StringContext, default_max_load_percentage);
}

/// Key memory is managed by the caller.  Keys and values
/// will not automatically be freed.
pub fn StringHashMapUnmanaged(comptime V: type) type {
    return HashMapUnmanaged([]const u8, V, StringContext, default_max_load_percentage);
}

pub const StringContext = struct {
    pub fn hash(self: @This(), s: []const u8) u64 {
        _ = self;
        return hashString(s);
    }
    pub fn eql(self: @This(), a: []const u8, b: []const u8) bool {
        _ = self;
        return eqlString(a, b);
    }
};

pub fn eqlString(a: []const u8, b: []const u8) bool {
    return mem.eql(u8, a, b);
}

pub fn hashString(s: []const u8) u64 {
    return std.hash.Wyhash.hash(0, s);
}

pub const StringIndexContext = struct {
    bytes: *const std.ArrayListUnmanaged(u8),

    pub fn eql(self: @This(), a: u32, b: u32) bool {
        _ = self;
        return a == b;
    }

    pub fn hash(self: @This(), x: u32) u64 {
        const x_slice = mem.sliceTo(@as([*:0]const u8, @ptrCast(self.bytes.items.ptr)) + x, 0);
        return hashString(x_slice);
    }
};

pub const StringIndexAdapter = struct {
    bytes: *const std.ArrayListUnmanaged(u8),

    pub fn eql(self: @This(), a_slice: []const u8, b: u32) bool {
        const b_slice = mem.sliceTo(@as([*:0]const u8, @ptrCast(self.bytes.items.ptr)) + b, 0);
        return mem.eql(u8, a_slice, b_slice);
    }

    pub fn hash(self: @This(), adapted_key: []const u8) u64 {
        _ = self;
        return hashString(adapted_key);
    }
};

pub const default_max_load_percentage = 80;

/// This function issues a compile error with a helpful message if there
/// is a problem with the provided context type.  A context must have the following
/// member functions:
///   - hash(self, PseudoKey) Hash
///   - eql(self, PseudoKey, Key) bool
///
/// If you are passing a context to a *Adapted function, PseudoKey is the type
/// of the key parameter.  Otherwise, when creating a HashMap or HashMapUnmanaged
/// type, PseudoKey = Key = K.
pub fn verifyContext(
    comptime RawContext: type,
    comptime PseudoKey: type,
    comptime Key: type,
    comptime Hash: type,
    comptime is_array: bool,
) void {
    comptime {
        var allow_const_ptr = false;
        var allow_mutable_ptr = false;
        // Context is the actual namespace type.  RawContext may be a pointer to Context.
        var Context = RawContext;
        // Make sure the context is a namespace type which may have member functions
        switch (@typeInfo(Context)) {
            .Struct, .Union, .Enum => {},
            // Special-case .Opaque for a better error message
            .Opaque => @compileError("Hash context must be a type with hash and eql member functions.  Cannot use " ++ @typeName(Context) ++ " because it is opaque.  Use a pointer instead."),
            .Pointer => |ptr| {
                if (ptr.size != .One) {
                    @compileError("Hash context must be a type with hash and eql member functions.  Cannot use " ++ @typeName(Context) ++ " because it is not a single pointer.");
                }
                Context = ptr.child;
                allow_const_ptr = true;
                allow_mutable_ptr = !ptr.is_const;
                switch (@typeInfo(Context)) {
                    .Struct, .Union, .Enum, .Opaque => {},
                    else => @compileError("Hash context must be a type with hash and eql member functions.  Cannot use " ++ @typeName(Context)),
                }
            },
            else => @compileError("Hash context must be a type with hash and eql member functions.  Cannot use " ++ @typeName(Context)),
        }

        // Keep track of multiple errors so we can report them all.
        var errors: []const u8 = "";

        // Put common errors here, they will only be evaluated
        // if the error is actually triggered.
        const lazy = struct {
            const prefix = "\n  ";
            const deep_prefix = prefix ++ "  ";
            const hash_signature = "fn (self, " ++ @typeName(PseudoKey) ++ ") " ++ @typeName(Hash);
            const index_param = if (is_array) ", b_index: usize" else "";
            const eql_signature = "fn (self, " ++ @typeName(PseudoKey) ++ ", " ++
                @typeName(Key) ++ index_param ++ ") bool";
            const err_invalid_hash_signature = prefix ++ @typeName(Context) ++ ".hash must be " ++ hash_signature ++
                deep_prefix ++ "but is actually " ++ @typeName(@TypeOf(Context.hash));
            const err_invalid_eql_signature = prefix ++ @typeName(Context) ++ ".eql must be " ++ eql_signature ++
                deep_prefix ++ "but is actually " ++ @typeName(@TypeOf(Context.eql));
        };

        // Verify Context.hash(self, PseudoKey) => Hash
        if (@hasDecl(Context, "hash")) {
            const hash = Context.hash;
            const info = @typeInfo(@TypeOf(hash));
            if (info == .Fn) {
                const func = info.Fn;
                if (func.params.len != 2) {
                    errors = errors ++ lazy.err_invalid_hash_signature;
                } else {
                    var emitted_signature = false;
                    if (func.params[0].type) |Self| {
                        if (Self == Context) {
                            // pass, this is always fine.
                        } else if (Self == *const Context) {
                            if (!allow_const_ptr) {
                                if (!emitted_signature) {
                                    errors = errors ++ lazy.err_invalid_hash_signature;
                                    emitted_signature = true;
                                }
                                errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ ", but is " ++ @typeName(Self);
                                errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be a pointer because it is passed by value.";
                            }
                        } else if (Self == *Context) {
                            if (!allow_mutable_ptr) {
                                if (!emitted_signature) {
                                    errors = errors ++ lazy.err_invalid_hash_signature;
                                    emitted_signature = true;
                                }
                                if (!allow_const_ptr) {
                                    errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ ", but is " ++ @typeName(Self);
                                    errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be a pointer because it is passed by value.";
                                } else {
                                    errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ " or " ++ @typeName(*const Context) ++ ", but is " ++ @typeName(Self);
                                    errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be non-const because it is passed by const pointer.";
                                }
                            }
                        } else {
                            if (!emitted_signature) {
                                errors = errors ++ lazy.err_invalid_hash_signature;
                                emitted_signature = true;
                            }
                            errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context);
                            if (allow_const_ptr) {
                                errors = errors ++ " or " ++ @typeName(*const Context);
                                if (allow_mutable_ptr) {
                                    errors = errors ++ " or " ++ @typeName(*Context);
                                }
                            }
                            errors = errors ++ ", but is " ++ @typeName(Self);
                        }
                    }
                    if (func.params[1].type != null and func.params[1].type.? != PseudoKey) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_hash_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Second parameter must be " ++ @typeName(PseudoKey) ++ ", but is " ++ @typeName(func.params[1].type.?);
                    }
                    if (func.return_type != null and func.return_type.? != Hash) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_hash_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Return type must be " ++ @typeName(Hash) ++ ", but was " ++ @typeName(func.return_type.?);
                    }
                    // If any of these are generic (null), we cannot verify them.
                    // The call sites check the return type, but cannot check the
                    // parameters.  This may cause compile errors with generic hash/eql functions.
                }
            } else {
                errors = errors ++ lazy.err_invalid_hash_signature;
            }
        } else {
            errors = errors ++ lazy.prefix ++ @typeName(Context) ++ " must declare a pub hash function with signature " ++ lazy.hash_signature;
        }

        // Verify Context.eql(self, PseudoKey, Key) => bool
        if (@hasDecl(Context, "eql")) {
            const eql = Context.eql;
            const info = @typeInfo(@TypeOf(eql));
            if (info == .Fn) {
                const func = info.Fn;
                const args_len = if (is_array) 4 else 3;
                if (func.params.len != args_len) {
                    errors = errors ++ lazy.err_invalid_eql_signature;
                } else {
                    var emitted_signature = false;
                    if (func.params[0].type) |Self| {
                        if (Self == Context) {
                            // pass, this is always fine.
                        } else if (Self == *const Context) {
                            if (!allow_const_ptr) {
                                if (!emitted_signature) {
                                    errors = errors ++ lazy.err_invalid_eql_signature;
                                    emitted_signature = true;
                                }
                                errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ ", but is " ++ @typeName(Self);
                                errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be a pointer because it is passed by value.";
                            }
                        } else if (Self == *Context) {
                            if (!allow_mutable_ptr) {
                                if (!emitted_signature) {
                                    errors = errors ++ lazy.err_invalid_eql_signature;
                                    emitted_signature = true;
                                }
                                if (!allow_const_ptr) {
                                    errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ ", but is " ++ @typeName(Self);
                                    errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be a pointer because it is passed by value.";
                                } else {
                                    errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ " or " ++ @typeName(*const Context) ++ ", but is " ++ @typeName(Self);
                                    errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be non-const because it is passed by const pointer.";
                                }
                            }
                        } else {
                            if (!emitted_signature) {
                                errors = errors ++ lazy.err_invalid_eql_signature;
                                emitted_signature = true;
                            }
                            errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context);
                            if (allow_const_ptr) {
                                errors = errors ++ " or " ++ @typeName(*const Context);
                                if (allow_mutable_ptr) {
                                    errors = errors ++ " or " ++ @typeName(*Context);
                                }
                            }
                            errors = errors ++ ", but is " ++ @typeName(Self);
                        }
                    }
                    if (func.params[1].type.? != PseudoKey) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_eql_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Second parameter must be " ++ @typeName(PseudoKey) ++ ", but is " ++ @typeName(func.params[1].type.?);
                    }
                    if (func.params[2].type.? != Key) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_eql_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Third parameter must be " ++ @typeName(Key) ++ ", but is " ++ @typeName(func.params[2].type.?);
                    }
                    if (func.return_type.? != bool) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_eql_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Return type must be bool, but was " ++ @typeName(func.return_type.?);
                    }
                    // If any of these are generic (null), we cannot verify them.
                    // The call sites check the return type, but cannot check the
                    // parameters.  This may cause compile errors with generic hash/eql functions.
                }
            } else {
                errors = errors ++ lazy.err_invalid_eql_signature;
            }
        } else {
            errors = errors ++ lazy.prefix ++ @typeName(Context) ++ " must declare a pub eql function with signature " ++ lazy.eql_signature;
        }

        if (errors.len != 0) {
            // errors begins with a newline (from lazy.prefix)
            @compileError("Problems found with hash context type " ++ @typeName(Context) ++ ":" ++ errors);
        }
    }
}

/// General purpose hash table.
/// No order is guaranteed and any modification invalidates live iterators.
/// It provides fast operations (lookup, insertion, deletion) with quite high
/// load factors (up to 80% by default) for low memory usage.
/// For a hash map that can be initialized directly that does not store an Allocator
/// field, see `HashMapUnmanaged`.
/// If iterating over the table entries is a strong usecase and needs to be fast,
/// prefer the alternative `std.ArrayHashMap`.
/// Context must be a struct type with two member functions:
///   hash(self, K) u64
///   eql(self, K, K) bool
/// Adapted variants of many functions are provided.  These variants
/// take a pseudo key instead of a key.  Their context must have the functions:
///   hash(self, PseudoKey) u64
///   eql(self, PseudoKey, K) bool
pub fn HashMap(
=======
/// Builtin hashmap for strings as keys.
/// Key memory is managed by the caller.  Keys and values
/// will not automatically be freed.
pub fn StringHashMap(comptime V: type) type {
    return HashMap([]const u8, V, StringContext, default_max_load_percentage);
}

/// Key memory is managed by the caller.  Keys and values
/// will not automatically be freed.
pub fn StringHashMapUnmanaged(comptime V: type) type {
    return HashMapUnmanaged([]const u8, V, StringContext, default_max_load_percentage);
}

pub const StringContext = struct {
    pub fn hash(self: @This(), s: []const u8) u64 {
        _ = self;
        return hashString(s);
    }
    pub fn eql(self: @This(), a: []const u8, b: []const u8) bool {
        _ = self;
        return eqlString(a, b);
    }
};

pub fn eqlString(a: []const u8, b: []const u8) bool {
    return mem.eql(u8, a, b);
}

pub fn hashString(s: []const u8) u64 {
    return std.hash.Wyhash.hash(0, s);
}

pub const StringIndexContext = struct {
    bytes: *const std.ArrayListUnmanaged(u8),

    pub fn eql(_: @This(), a: u32, b: u32) bool {
        return a == b;
    }

    pub fn hash(ctx: @This(), key: u32) u64 {
        return hashString(mem.sliceTo(ctx.bytes.items[key..], 0));
    }
};

pub const StringIndexAdapter = struct {
    bytes: *const std.ArrayListUnmanaged(u8),

    pub fn eql(ctx: @This(), a: []const u8, b: u32) bool {
        return mem.eql(u8, a, mem.sliceTo(ctx.bytes.items[b..], 0));
    }

    pub fn hash(_: @This(), adapted_key: []const u8) u64 {
        assert(mem.indexOfScalar(u8, adapted_key, 0) == null);
        return hashString(adapted_key);
    }
};

pub const default_max_load_percentage = 80;

/// General purpose hash table.
/// No order is guaranteed and any modification invalidates live iterators.
/// It provides fast operations (lookup, insertion, deletion) with quite high
/// load factors (up to 80% by default) for low memory usage.
/// For a hash map that can be initialized directly that does not store an Allocator
/// field, see `HashMapUnmanaged`.
/// If iterating over the table entries is a strong usecase and needs to be fast,
/// prefer the alternative `std.ArrayHashMap`.
/// Context must be a struct type with two member functions:
///   hash(self, K) u64
///   eql(self, K, K) bool
/// Adapted variants of many functions are provided.  These variants
/// take a pseudo key instead of a key.  Their context must have the functions:
///   hash(self, PseudoKey) u64
///   eql(self, PseudoKey, K) bool
pub fn HashMap(
>>>>>>> theirs
    comptime K: type,
    comptime V: type,
    comptime Context: type,
) type {
    return struct {
<<<<<<< ours
||||||| base
        unmanaged: Unmanaged,
        allocator: Allocator,
        ctx: Context,

        comptime {
            verifyContext(Context, K, K, u64, false);
        }

        /// The type of the unmanaged hash map underlying this wrapper
        pub const Unmanaged = HashMapUnmanaged(K, V, Context, max_load_percentage);
        /// An entry, containing pointers to a key and value stored in the map
        pub const Entry = Unmanaged.Entry;
        /// A copy of a key and value which are no longer in the map
        pub const KV = Unmanaged.KV;
        /// The integer type that is the result of hashing
        pub const Hash = Unmanaged.Hash;
        /// The iterator type returned by iterator()
        pub const Iterator = Unmanaged.Iterator;

        pub const KeyIterator = Unmanaged.KeyIterator;
        pub const ValueIterator = Unmanaged.ValueIterator;

        /// The integer type used to store the size of the map
        pub const Size = Unmanaged.Size;
        /// The type returned from getOrPut and variants
        pub const GetOrPutResult = Unmanaged.GetOrPutResult;

=======
        unmanaged: Unmanaged,
        allocator: Allocator,
        ctx: Context,

        /// The type of the unmanaged hash map underlying this wrapper
        pub const Unmanaged = HashMapUnmanaged(K, V, Context, max_load_percentage);
        /// An entry, containing pointers to a key and value stored in the map
        pub const Entry = Unmanaged.Entry;
        /// A copy of a key and value which are no longer in the map
        pub const KV = Unmanaged.KV;
        /// The integer type that is the result of hashing
        pub const Hash = Unmanaged.Hash;
        /// The iterator type returned by iterator()
        pub const Iterator = Unmanaged.Iterator;

        pub const KeyIterator = Unmanaged.KeyIterator;
        pub const ValueIterator = Unmanaged.ValueIterator;

        /// The integer type used to store the size of the map
        pub const Size = Unmanaged.Size;
        /// The type returned from getOrPut and variants
        pub const GetOrPutResult = Unmanaged.GetOrPutResult;

>>>>>>> theirs
        const Self = @This();

<<<<<<< ours
        /// This is the pointer-based map that we're wrapping.
        pub const Unmanaged = HashMapUnmanaged(K, V, Context);
        pub const Layout = Unmanaged.Layout;
||||||| base
        /// Create a managed hash map with an empty context.
        /// If the context is not zero-sized, you must use
        /// initContext(allocator, ctx) instead.
        pub fn init(allocator: Allocator) Self {
            if (@sizeOf(Context) != 0) {
                @compileError("Context must be specified! Call initContext(allocator, ctx) instead.");
            }
            return .{
                .unmanaged = .{},
                .allocator = allocator,
                .ctx = undefined, // ctx is zero-sized so this is safe.
            };
        }

        /// Create a managed hash map with a context
        pub fn initContext(allocator: Allocator, ctx: Context) Self {
            return .{
                .unmanaged = .{},
                .allocator = allocator,
                .ctx = ctx,
            };
        }

        /// Release the backing array and invalidate this map.
        /// This does *not* deinit keys, values, or the context!
        /// If your keys or values need to be released, ensure
        /// that that is done before calling this function.
        pub fn deinit(self: *Self) void {
            self.unmanaged.deinit(self.allocator);
            self.* = undefined;
        }

        /// Empty the map, but keep the backing allocation for future use.
        /// This does *not* free keys or values! Be sure to
        /// release them if they need deinitialization before
        /// calling this function.
        pub fn clearRetainingCapacity(self: *Self) void {
            return self.unmanaged.clearRetainingCapacity();
        }

        /// Empty the map and release the backing allocation.
        /// This does *not* free keys or values! Be sure to
        /// release them if they need deinitialization before
        /// calling this function.
        pub fn clearAndFree(self: *Self) void {
            return self.unmanaged.clearAndFree(self.allocator);
        }
=======
        /// Create a managed hash map with an empty context.
        /// If the context is not zero-sized, you must use
        /// initContext(allocator, ctx) instead.
        pub fn init(allocator: Allocator) Self {
            if (@sizeOf(Context) != 0) {
                @compileError("Context must be specified! Call initContext(allocator, ctx) instead.");
            }
            return .{
                .unmanaged = .empty,
                .allocator = allocator,
                .ctx = undefined, // ctx is zero-sized so this is safe.
            };
        }

        /// Create a managed hash map with a context
        pub fn initContext(allocator: Allocator, ctx: Context) Self {
            return .{
                .unmanaged = .empty,
                .allocator = allocator,
                .ctx = ctx,
            };
        }

        /// Puts the hash map into a state where any method call that would
        /// cause an existing key or value pointer to become invalidated will
        /// instead trigger an assertion.
        ///
        /// An additional call to `lockPointers` in such state also triggers an
        /// assertion.
        ///
        /// `unlockPointers` returns the hash map to the previous state.
        pub fn lockPointers(self: *Self) void {
            self.unmanaged.lockPointers();
        }

        /// Undoes a call to `lockPointers`.
        pub fn unlockPointers(self: *Self) void {
            self.unmanaged.unlockPointers();
        }

        /// Release the backing array and invalidate this map.
        /// This does *not* deinit keys, values, or the context!
        /// If your keys or values need to be released, ensure
        /// that that is done before calling this function.
        pub fn deinit(self: *Self) void {
            self.unmanaged.deinit(self.allocator);
            self.* = undefined;
        }

        /// Empty the map, but keep the backing allocation for future use.
        /// This does *not* free keys or values! Be sure to
        /// release them if they need deinitialization before
        /// calling this function.
        pub fn clearRetainingCapacity(self: *Self) void {
            return self.unmanaged.clearRetainingCapacity();
        }

        /// Empty the map and release the backing allocation.
        /// This does *not* free keys or values! Be sure to
        /// release them if they need deinitialization before
        /// calling this function.
        pub fn clearAndFree(self: *Self) void {
            return self.unmanaged.clearAndFree(self.allocator);
        }
>>>>>>> theirs

        /// This is the alignment that the base pointer must have.
        pub const base_align = Unmanaged.base_align;

        metadata: Offset(Unmanaged.Metadata) = .{},

<<<<<<< ours
        /// Returns the total size of the backing memory required for a
        /// HashMap with the given capacity. The base ptr must also be
        /// aligned to base_align.
        pub fn layout(cap: Unmanaged.Size) Layout {
            return Unmanaged.layoutForCapacity(cap);
||||||| base
        /// Create an iterator over the keys in the map.
        /// The iterator is invalidated if the map is modified.
        pub fn keyIterator(self: *const Self) KeyIterator {
            return self.unmanaged.keyIterator();
=======
        /// Create an iterator over the keys in the map.
        /// The iterator is invalidated if the map is modified.
        pub fn keyIterator(self: Self) KeyIterator {
            return self.unmanaged.keyIterator();
>>>>>>> theirs
        }

<<<<<<< ours
        /// Initialize a new HashMap with the given capacity and backing
        /// memory. The backing memory must be aligned to base_align.
        pub fn init(buf: OffsetBuf, l: Layout) Self {
            assert(base_align.check(@intFromPtr(buf.start())));
||||||| base
        /// Create an iterator over the values in the map.
        /// The iterator is invalidated if the map is modified.
        pub fn valueIterator(self: *const Self) ValueIterator {
            return self.unmanaged.valueIterator();
        }
=======
        /// Create an iterator over the values in the map.
        /// The iterator is invalidated if the map is modified.
        pub fn valueIterator(self: Self) ValueIterator {
            return self.unmanaged.valueIterator();
        }
>>>>>>> theirs

            const m = Unmanaged.init(buf, l);
            return .{ .metadata = getOffset(
                Unmanaged.Metadata,
                buf,
                @ptrCast(m.metadata.?),
            ) };
        }

<<<<<<< ours
        /// Returns the pointer-based map from a base pointer.
        pub fn map(self: Self, base: anytype) Unmanaged {
            return .{ .metadata = self.metadata.ptr(base) };
||||||| base
        /// If there is an existing item with `key`, then the result's
        /// `Entry` pointers point to it, and found_existing is true.
        /// Otherwise, puts a new item with undefined value, and
        /// the `Entry` pointers point to it. Caller must then initialize
        /// the key and value.
        /// If a new entry needs to be stored, this function asserts there
        /// is enough capacity to store it.
        pub fn getOrPutAssumeCapacityAdapted(self: *Self, key: anytype, ctx: anytype) GetOrPutResult {
            return self.unmanaged.getOrPutAssumeCapacityAdapted(key, ctx);
        }

        pub fn getOrPutValue(self: *Self, key: K, value: V) Allocator.Error!Entry {
            return self.unmanaged.getOrPutValueContext(self.allocator, key, value, self.ctx);
        }

        /// Increases capacity, guaranteeing that insertions up until the
        /// `expected_count` will not cause an allocation, and therefore cannot fail.
        pub fn ensureTotalCapacity(self: *Self, expected_count: Size) Allocator.Error!void {
            return self.unmanaged.ensureTotalCapacityContext(self.allocator, expected_count, self.ctx);
        }

        /// Increases capacity, guaranteeing that insertions up until
        /// `additional_count` **more** items will not cause an allocation, and
        /// therefore cannot fail.
        pub fn ensureUnusedCapacity(self: *Self, additional_count: Size) Allocator.Error!void {
            return self.unmanaged.ensureUnusedCapacityContext(self.allocator, additional_count, self.ctx);
        }

        /// Returns the number of total elements which may be present before it is
        /// no longer guaranteed that no allocations will be performed.
        pub fn capacity(self: *Self) Size {
            return self.unmanaged.capacity();
        }

        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPut`.
        pub fn put(self: *Self, key: K, value: V) Allocator.Error!void {
            return self.unmanaged.putContext(self.allocator, key, value, self.ctx);
        }

        /// Inserts a key-value pair into the hash map, asserting that no previous
        /// entry with the same key is already present
        pub fn putNoClobber(self: *Self, key: K, value: V) Allocator.Error!void {
            return self.unmanaged.putNoClobberContext(self.allocator, key, value, self.ctx);
        }

        /// Asserts there is enough capacity to store the new key-value pair.
        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPutAssumeCapacity`.
        pub fn putAssumeCapacity(self: *Self, key: K, value: V) void {
            return self.unmanaged.putAssumeCapacityContext(key, value, self.ctx);
        }

        /// Asserts there is enough capacity to store the new key-value pair.
        /// Asserts that it does not clobber any existing data.
        /// To detect if a put would clobber existing data, see `getOrPutAssumeCapacity`.
        pub fn putAssumeCapacityNoClobber(self: *Self, key: K, value: V) void {
            return self.unmanaged.putAssumeCapacityNoClobberContext(key, value, self.ctx);
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        pub fn fetchPut(self: *Self, key: K, value: V) Allocator.Error!?KV {
            return self.unmanaged.fetchPutContext(self.allocator, key, value, self.ctx);
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        /// If insertion happens, asserts there is enough capacity without allocating.
        pub fn fetchPutAssumeCapacity(self: *Self, key: K, value: V) ?KV {
            return self.unmanaged.fetchPutAssumeCapacityContext(key, value, self.ctx);
        }

        /// Removes a value from the map and returns the removed kv pair.
        pub fn fetchRemove(self: *Self, key: K) ?KV {
            return self.unmanaged.fetchRemoveContext(key, self.ctx);
        }

        pub fn fetchRemoveAdapted(self: *Self, key: anytype, ctx: anytype) ?KV {
            return self.unmanaged.fetchRemoveAdapted(key, ctx);
        }

        /// Finds the value associated with a key in the map
        pub fn get(self: Self, key: K) ?V {
            return self.unmanaged.getContext(key, self.ctx);
        }
        pub fn getAdapted(self: Self, key: anytype, ctx: anytype) ?V {
            return self.unmanaged.getAdapted(key, ctx);
        }

        pub fn getPtr(self: Self, key: K) ?*V {
            return self.unmanaged.getPtrContext(key, self.ctx);
        }
        pub fn getPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*V {
            return self.unmanaged.getPtrAdapted(key, ctx);
        }

        /// Finds the actual key associated with an adapted key in the map
        pub fn getKey(self: Self, key: K) ?K {
            return self.unmanaged.getKeyContext(key, self.ctx);
        }
        pub fn getKeyAdapted(self: Self, key: anytype, ctx: anytype) ?K {
            return self.unmanaged.getKeyAdapted(key, ctx);
        }

        pub fn getKeyPtr(self: Self, key: K) ?*K {
            return self.unmanaged.getKeyPtrContext(key, self.ctx);
        }
        pub fn getKeyPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*K {
            return self.unmanaged.getKeyPtrAdapted(key, ctx);
        }

        /// Finds the key and value associated with a key in the map
        pub fn getEntry(self: Self, key: K) ?Entry {
            return self.unmanaged.getEntryContext(key, self.ctx);
        }

        pub fn getEntryAdapted(self: Self, key: anytype, ctx: anytype) ?Entry {
            return self.unmanaged.getEntryAdapted(key, ctx);
        }

        /// Check if the map contains a key
        pub fn contains(self: Self, key: K) bool {
            return self.unmanaged.containsContext(key, self.ctx);
        }

        pub fn containsAdapted(self: Self, key: anytype, ctx: anytype) bool {
            return self.unmanaged.containsAdapted(key, ctx);
        }

        /// If there is an `Entry` with a matching key, it is deleted from
        /// the hash map, and this function returns true.  Otherwise this
        /// function returns false.
        pub fn remove(self: *Self, key: K) bool {
            return self.unmanaged.removeContext(key, self.ctx);
        }

        pub fn removeAdapted(self: *Self, key: anytype, ctx: anytype) bool {
            return self.unmanaged.removeAdapted(key, ctx);
        }

        /// Delete the entry with key pointed to by key_ptr from the hash map.
        /// key_ptr is assumed to be a valid pointer to a key that is present
        /// in the hash map.
        pub fn removeByPtr(self: *Self, key_ptr: *K) void {
            self.unmanaged.removeByPtr(key_ptr);
        }

        /// Creates a copy of this map, using the same allocator
        pub fn clone(self: Self) Allocator.Error!Self {
            var other = try self.unmanaged.cloneContext(self.allocator, self.ctx);
            return other.promoteContext(self.allocator, self.ctx);
        }

        /// Creates a copy of this map, using a specified allocator
        pub fn cloneWithAllocator(self: Self, new_allocator: Allocator) Allocator.Error!Self {
            var other = try self.unmanaged.cloneContext(new_allocator, self.ctx);
            return other.promoteContext(new_allocator, self.ctx);
        }

        /// Creates a copy of this map, using a specified context
        pub fn cloneWithContext(self: Self, new_ctx: anytype) Allocator.Error!HashMap(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other = try self.unmanaged.cloneContext(self.allocator, new_ctx);
            return other.promoteContext(self.allocator, new_ctx);
        }

        /// Creates a copy of this map, using a specified allocator and context.
        pub fn cloneWithAllocatorAndContext(
            self: Self,
            new_allocator: Allocator,
            new_ctx: anytype,
        ) Allocator.Error!HashMap(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other = try self.unmanaged.cloneContext(new_allocator, new_ctx);
            return other.promoteContext(new_allocator, new_ctx);
        }

        /// Set the map to an empty state, making deinitialization a no-op, and
        /// returning a copy of the original.
        pub fn move(self: *Self) Self {
            const result = self.*;
            self.unmanaged = .{};
            return result;
=======
        /// If there is an existing item with `key`, then the result's
        /// `Entry` pointers point to it, and found_existing is true.
        /// Otherwise, puts a new item with undefined value, and
        /// the `Entry` pointers point to it. Caller must then initialize
        /// the key and value.
        /// If a new entry needs to be stored, this function asserts there
        /// is enough capacity to store it.
        pub fn getOrPutAssumeCapacityAdapted(self: *Self, key: anytype, ctx: anytype) GetOrPutResult {
            return self.unmanaged.getOrPutAssumeCapacityAdapted(key, ctx);
        }

        pub fn getOrPutValue(self: *Self, key: K, value: V) Allocator.Error!Entry {
            return self.unmanaged.getOrPutValueContext(self.allocator, key, value, self.ctx);
        }

        /// Increases capacity, guaranteeing that insertions up until the
        /// `expected_count` will not cause an allocation, and therefore cannot fail.
        pub fn ensureTotalCapacity(self: *Self, expected_count: Size) Allocator.Error!void {
            return self.unmanaged.ensureTotalCapacityContext(self.allocator, expected_count, self.ctx);
        }

        /// Increases capacity, guaranteeing that insertions up until
        /// `additional_count` **more** items will not cause an allocation, and
        /// therefore cannot fail.
        pub fn ensureUnusedCapacity(self: *Self, additional_count: Size) Allocator.Error!void {
            return self.unmanaged.ensureUnusedCapacityContext(self.allocator, additional_count, self.ctx);
        }

        /// Returns the number of total elements which may be present before it is
        /// no longer guaranteed that no allocations will be performed.
        pub fn capacity(self: Self) Size {
            return self.unmanaged.capacity();
        }

        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPut`.
        pub fn put(self: *Self, key: K, value: V) Allocator.Error!void {
            return self.unmanaged.putContext(self.allocator, key, value, self.ctx);
        }

        /// Inserts a key-value pair into the hash map, asserting that no previous
        /// entry with the same key is already present
        pub fn putNoClobber(self: *Self, key: K, value: V) Allocator.Error!void {
            return self.unmanaged.putNoClobberContext(self.allocator, key, value, self.ctx);
        }

        /// Asserts there is enough capacity to store the new key-value pair.
        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPutAssumeCapacity`.
        pub fn putAssumeCapacity(self: *Self, key: K, value: V) void {
            return self.unmanaged.putAssumeCapacityContext(key, value, self.ctx);
        }

        /// Asserts there is enough capacity to store the new key-value pair.
        /// Asserts that it does not clobber any existing data.
        /// To detect if a put would clobber existing data, see `getOrPutAssumeCapacity`.
        pub fn putAssumeCapacityNoClobber(self: *Self, key: K, value: V) void {
            return self.unmanaged.putAssumeCapacityNoClobberContext(key, value, self.ctx);
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        pub fn fetchPut(self: *Self, key: K, value: V) Allocator.Error!?KV {
            return self.unmanaged.fetchPutContext(self.allocator, key, value, self.ctx);
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        /// If insertion happens, asserts there is enough capacity without allocating.
        pub fn fetchPutAssumeCapacity(self: *Self, key: K, value: V) ?KV {
            return self.unmanaged.fetchPutAssumeCapacityContext(key, value, self.ctx);
        }

        /// Removes a value from the map and returns the removed kv pair.
        pub fn fetchRemove(self: *Self, key: K) ?KV {
            return self.unmanaged.fetchRemoveContext(key, self.ctx);
        }

        pub fn fetchRemoveAdapted(self: *Self, key: anytype, ctx: anytype) ?KV {
            return self.unmanaged.fetchRemoveAdapted(key, ctx);
        }

        /// Finds the value associated with a key in the map
        pub fn get(self: Self, key: K) ?V {
            return self.unmanaged.getContext(key, self.ctx);
        }
        pub fn getAdapted(self: Self, key: anytype, ctx: anytype) ?V {
            return self.unmanaged.getAdapted(key, ctx);
        }

        pub fn getPtr(self: Self, key: K) ?*V {
            return self.unmanaged.getPtrContext(key, self.ctx);
        }
        pub fn getPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*V {
            return self.unmanaged.getPtrAdapted(key, ctx);
        }

        /// Finds the actual key associated with an adapted key in the map
        pub fn getKey(self: Self, key: K) ?K {
            return self.unmanaged.getKeyContext(key, self.ctx);
        }
        pub fn getKeyAdapted(self: Self, key: anytype, ctx: anytype) ?K {
            return self.unmanaged.getKeyAdapted(key, ctx);
        }

        pub fn getKeyPtr(self: Self, key: K) ?*K {
            return self.unmanaged.getKeyPtrContext(key, self.ctx);
        }
        pub fn getKeyPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*K {
            return self.unmanaged.getKeyPtrAdapted(key, ctx);
        }

        /// Finds the key and value associated with a key in the map
        pub fn getEntry(self: Self, key: K) ?Entry {
            return self.unmanaged.getEntryContext(key, self.ctx);
        }

        pub fn getEntryAdapted(self: Self, key: anytype, ctx: anytype) ?Entry {
            return self.unmanaged.getEntryAdapted(key, ctx);
        }

        /// Check if the map contains a key
        pub fn contains(self: Self, key: K) bool {
            return self.unmanaged.containsContext(key, self.ctx);
        }

        pub fn containsAdapted(self: Self, key: anytype, ctx: anytype) bool {
            return self.unmanaged.containsAdapted(key, ctx);
        }

        /// If there is an `Entry` with a matching key, it is deleted from
        /// the hash map, and this function returns true.  Otherwise this
        /// function returns false.
        ///
        /// TODO: answer the question in these doc comments, does this
        /// increase the unused capacity by one?
        pub fn remove(self: *Self, key: K) bool {
            return self.unmanaged.removeContext(key, self.ctx);
        }

        /// TODO: answer the question in these doc comments, does this
        /// increase the unused capacity by one?
        pub fn removeAdapted(self: *Self, key: anytype, ctx: anytype) bool {
            return self.unmanaged.removeAdapted(key, ctx);
        }

        /// Delete the entry with key pointed to by key_ptr from the hash map.
        /// key_ptr is assumed to be a valid pointer to a key that is present
        /// in the hash map.
        ///
        /// TODO: answer the question in these doc comments, does this
        /// increase the unused capacity by one?
        pub fn removeByPtr(self: *Self, key_ptr: *K) void {
            self.unmanaged.removeByPtr(key_ptr);
        }

        /// Creates a copy of this map, using the same allocator
        pub fn clone(self: Self) Allocator.Error!Self {
            var other = try self.unmanaged.cloneContext(self.allocator, self.ctx);
            return other.promoteContext(self.allocator, self.ctx);
        }

        /// Creates a copy of this map, using a specified allocator
        pub fn cloneWithAllocator(self: Self, new_allocator: Allocator) Allocator.Error!Self {
            var other = try self.unmanaged.cloneContext(new_allocator, self.ctx);
            return other.promoteContext(new_allocator, self.ctx);
        }

        /// Creates a copy of this map, using a specified context
        pub fn cloneWithContext(self: Self, new_ctx: anytype) Allocator.Error!HashMap(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other = try self.unmanaged.cloneContext(self.allocator, new_ctx);
            return other.promoteContext(self.allocator, new_ctx);
        }

        /// Creates a copy of this map, using a specified allocator and context.
        pub fn cloneWithAllocatorAndContext(
            self: Self,
            new_allocator: Allocator,
            new_ctx: anytype,
        ) Allocator.Error!HashMap(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other = try self.unmanaged.cloneContext(new_allocator, new_ctx);
            return other.promoteContext(new_allocator, new_ctx);
        }

        /// Set the map to an empty state, making deinitialization a no-op, and
        /// returning a copy of the original.
        pub fn move(self: *Self) Self {
            self.unmanaged.pointer_stability.assertUnlocked();
            const result = self.*;
            self.unmanaged = .empty;
            return result;
>>>>>>> theirs
        }

        /// Rehash the map, in-place.
        ///
        /// Over time, due to the current tombstone-based implementation, a
        /// HashMap could become fragmented due to the buildup of tombstone
        /// entries that causes a performance degradation due to excessive
        /// probing. The kind of pattern that might cause this is a long-lived
        /// HashMap with repeated inserts and deletes.
        ///
        /// After this function is called, there will be no tombstones in
        /// the HashMap, each of the entries is rehashed and any existing
        /// key/value pointers into the HashMap are invalidated.
        pub fn rehash(self: *Self) void {
            self.unmanaged.rehash(self.ctx);
        }
    };
}

<<<<<<< ours
/// Fork of stdlib.HashMap as of Zig 0.12 modified to to use offsets
/// for the key/values pointer. The metadata is still a pointer to limit
/// the amount of arithmetic required to access it. See the file comment
/// for full details.
fn HashMapUnmanaged(
||||||| base
/// A HashMap based on open addressing and linear probing.
/// A lookup or modification typically incurs only 2 cache misses.
/// No order is guaranteed and any modification invalidates live iterators.
/// It achieves good performance with quite high load factors (by default,
/// grow is triggered at 80% full) and only one byte of overhead per element.
/// The struct itself is only 16 bytes for a small footprint. This comes at
/// the price of handling size with u32, which should be reasonable enough
/// for almost all uses.
/// Deletions are achieved with tombstones.
pub fn HashMapUnmanaged(
=======
/// A HashMap based on open addressing and linear probing.
/// A lookup or modification typically incurs only 2 cache misses.
/// No order is guaranteed and any modification invalidates live iterators.
/// It achieves good performance with quite high load factors (by default,
/// grow is triggered at 80% full) and only one byte of overhead per element.
/// The struct itself is only 16 bytes for a small footprint. This comes at
/// the price of handling size with u32, which should be reasonable enough
/// for almost all uses.
/// Deletions are achieved with tombstones.
///
/// Default initialization of this struct is deprecated; use `.empty` instead.
pub fn HashMapUnmanaged(
>>>>>>> theirs
    comptime K: type,
    comptime V: type,
    comptime Context: type,
) type {
    return struct {
        const Self = @This();

<<<<<<< ours
        comptime {
            assert(@alignOf(Metadata) == 1);
        }

        const header_align = @alignOf(Header);
        const key_align = if (@sizeOf(K) == 0) 1 else @alignOf(K);
        const val_align = if (@sizeOf(V) == 0) 1 else @alignOf(V);
        const base_align: mem.Alignment = .fromByteUnits(@max(
            header_align,
            key_align,
            val_align,
        ));

||||||| base
        comptime {
            verifyContext(Context, K, K, u64, false);
        }

=======
>>>>>>> theirs
        // This is actually a midway pointer to the single buffer containing
        // a `Header` field, the `Metadata`s and `Entry`s.
        // At `-@sizeOf(Header)` is the Header field.
        // At `sizeOf(Metadata) * capacity + offset`, which is pointed to by
        // self.header().entries, is the array of entries.
        // This means that the hashmap only holds one live allocation, to
        // reduce memory fragmentation and struct size.
        /// Pointer to the metadata.
        metadata: ?[*]Metadata = null,

<<<<<<< ours
||||||| base
        /// Current number of elements in the hashmap.
        size: Size = 0,

        // Having a countdown to grow reduces the number of instructions to
        // execute when determining if the hashmap has enough capacity already.
        /// Number of available slots before a grow is needed to satisfy the
        /// `max_load_percentage`.
        available: Size = 0,

=======
        /// Current number of elements in the hashmap.
        size: Size = 0,

        // Having a countdown to grow reduces the number of instructions to
        // execute when determining if the hashmap has enough capacity already.
        /// Number of available slots before a grow is needed to satisfy the
        /// `max_load_percentage`.
        available: Size = 0,

        /// Used to detect memory safety violations.
        pointer_stability: std.debug.SafetyLock = .{},

>>>>>>> theirs
        // This is purely empirical and not a /very smart magic constant™/.
        /// Capacity of the first grow when bootstrapping the hashmap.
        const minimal_capacity = 8;

        /// A map containing no keys or values.
        pub const empty: Self = .{
            .metadata = null,
            .size = 0,
            .available = 0,
        };

        // This hashmap is specially designed for sizes that fit in a u32.
        pub const Size = u32;

        // u64 hashes guarantee us that the fingerprint bits will never be used
        // to compute the index of a slot, maximizing the use of entropy.
        pub const Hash = u64;

        pub const Entry = struct {
            key_ptr: *K,
            value_ptr: *V,
        };

        pub const KV = struct {
            key: K,
            value: V,
        };

        const Header = struct {
            /// The keys/values offset are relative to the metadata
            values: Offset(V),
            keys: Offset(K),
            capacity: Size,
            size: Size,
        };

        /// Metadata for a slot. It can be in three states: empty, used or
        /// tombstone. Tombstones indicate that an entry was previously used,
        /// they are a simple way to handle removal.
        /// To this state, we add 7 bits from the slot's key hash. These are
        /// used as a fast way to disambiguate between entries without
        /// having to use the equality function. If two fingerprints are
        /// different, we know that we don't have to compare the keys at all.
        /// The 7 bits are the highest ones from a 64 bit hash. This way, not
        /// only we use the `log2(capacity)` lowest bits from the hash to determine
        /// a slot index, but we use 7 more bits to quickly resolve collisions
        /// when multiple elements with different hashes end up wanting to be in the same slot.
        /// Not using the equality function means we don't have to read into
        /// the entries array, likely avoiding a cache miss and a potentially
        /// costly function call.
        const Metadata = packed struct {
            const FingerPrint = u7;

            const free: FingerPrint = 0;
            const tombstone: FingerPrint = 1;

            fingerprint: FingerPrint = free,
            used: u1 = 0,

            const slot_free = @as(u8, @bitCast(Metadata{ .fingerprint = free }));
            const slot_tombstone = @as(u8, @bitCast(Metadata{ .fingerprint = tombstone }));

            pub fn isUsed(self: Metadata) bool {
                return self.used == 1;
            }

            pub fn isTombstone(self: Metadata) bool {
                return @as(u8, @bitCast(self)) == slot_tombstone;
            }

            pub fn isFree(self: Metadata) bool {
                return @as(u8, @bitCast(self)) == slot_free;
            }

            pub fn takeFingerprint(hash: Hash) FingerPrint {
                const hash_bits = @typeInfo(Hash).int.bits;
                const fp_bits = @typeInfo(FingerPrint).int.bits;
                return @as(FingerPrint, @truncate(hash >> (hash_bits - fp_bits)));
            }

            pub fn fill(self: *Metadata, fp: FingerPrint) void {
                self.used = 1;
                self.fingerprint = fp;
            }

            pub fn remove(self: *Metadata) void {
                self.used = 0;
                self.fingerprint = tombstone;
            }
        };

        comptime {
            assert(@sizeOf(Metadata) == 1);
            assert(@alignOf(Metadata) == 1);
        }

        pub const Iterator = struct {
            hm: *const Self,
            index: Size = 0,

            pub fn next(it: *Iterator) ?Entry {
                assert(it.index <= it.hm.capacity());
                if (it.hm.header().size == 0) return null;

                const cap = it.hm.capacity();
                const end = it.hm.metadata.? + cap;
                var metadata = it.hm.metadata.? + it.index;

                while (metadata != end) : ({
                    metadata += 1;
                    it.index += 1;
                }) {
                    if (metadata[0].isUsed()) {
                        const key = &it.hm.keys()[it.index];
                        const value = &it.hm.values()[it.index];
                        it.index += 1;
                        return Entry{ .key_ptr = key, .value_ptr = value };
                    }
                }

                return null;
            }
        };

        pub const KeyIterator = FieldIterator(K);
        pub const ValueIterator = FieldIterator(V);

        fn FieldIterator(comptime T: type) type {
            return struct {
                len: usize,
                metadata: [*]const Metadata,
                items: [*]T,

                pub fn next(self: *@This()) ?*T {
                    while (self.len > 0) {
                        self.len -= 1;
                        const used = self.metadata[0].isUsed();
                        const item = &self.items[0];
                        self.metadata += 1;
                        self.items += 1;
                        if (used) {
                            return item;
                        }
                    }
                    return null;
                }
            };
        }

        pub const GetOrPutResult = struct {
            key_ptr: *K,
            value_ptr: *V,
            found_existing: bool,
        };

<<<<<<< ours
        /// Initialize a hash map with a given capacity and a buffer. The
        /// buffer must fit within the size defined by `layoutForCapacity`.
        pub fn init(buf: OffsetBuf, layout: Layout) Self {
            assert(base_align.check(@intFromPtr(buf.start())));

            // Get all our main pointers
            const metadata_buf = buf.rebase(@sizeOf(Header));
            const metadata_ptr: [*]Metadata = @ptrCast(metadata_buf.start());

            // Build our map
            var map: Self = .{ .metadata = metadata_ptr };
            const hdr = map.header();
            hdr.capacity = layout.capacity;
            hdr.size = 0;
            if (@sizeOf([*]K) != 0) hdr.keys = metadata_buf.member(K, layout.keys_start);
            if (@sizeOf([*]V) != 0) hdr.values = metadata_buf.member(V, layout.vals_start);
            map.initMetadatas();
||||||| base
        pub const Managed = HashMap(K, V, Context, max_load_percentage);

        pub fn promote(self: Self, allocator: Allocator) Managed {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call promoteContext instead.");
            return promoteContext(self, allocator, undefined);
        }

        pub fn promoteContext(self: Self, allocator: Allocator, ctx: Context) Managed {
            return .{
                .unmanaged = self,
                .allocator = allocator,
                .ctx = ctx,
            };
        }

        fn isUnderMaxLoadPercentage(size: Size, cap: Size) bool {
            return size * 100 < max_load_percentage * cap;
        }

        pub fn deinit(self: *Self, allocator: Allocator) void {
            self.deallocate(allocator);
            self.* = undefined;
        }
=======
        pub const Managed = HashMap(K, V, Context, max_load_percentage);

        pub fn promote(self: Self, allocator: Allocator) Managed {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call promoteContext instead.");
            return promoteContext(self, allocator, undefined);
        }

        pub fn promoteContext(self: Self, allocator: Allocator, ctx: Context) Managed {
            return .{
                .unmanaged = self,
                .allocator = allocator,
                .ctx = ctx,
            };
        }

        /// Puts the hash map into a state where any method call that would
        /// cause an existing key or value pointer to become invalidated will
        /// instead trigger an assertion.
        ///
        /// An additional call to `lockPointers` in such state also triggers an
        /// assertion.
        ///
        /// `unlockPointers` returns the hash map to the previous state.
        pub fn lockPointers(self: *Self) void {
            self.pointer_stability.lock();
        }

        /// Undoes a call to `lockPointers`.
        pub fn unlockPointers(self: *Self) void {
            self.pointer_stability.unlock();
        }

        fn isUnderMaxLoadPercentage(size: Size, cap: Size) bool {
            return size * 100 < max_load_percentage * cap;
        }

        pub fn deinit(self: *Self, allocator: Allocator) void {
            self.pointer_stability.assertUnlocked();
            self.deallocate(allocator);
            self.* = undefined;
        }
>>>>>>> theirs

<<<<<<< ours
            return map;
||||||| base
        fn capacityForSize(size: Size) Size {
            var new_cap: u32 = @truncate((@as(u64, size) * 100) / max_load_percentage + 1);
            new_cap = math.ceilPowerOfTwo(u32, new_cap) catch unreachable;
            return new_cap;
=======
        fn capacityForSize(size: Size) Size {
            var new_cap: u32 = @intCast((@as(u64, size) * 100) / max_load_percentage + 1);
            new_cap = math.ceilPowerOfTwo(u32, new_cap) catch unreachable;
            return new_cap;
>>>>>>> theirs
        }

<<<<<<< ours
        pub fn ensureTotalCapacity(self: *Self, new_size: Size) Allocator.Error!void {
            if (new_size > self.header().size) {
                try self.growIfNeeded(new_size - self.header().size);
            }
||||||| base
        pub fn ensureTotalCapacity(self: *Self, allocator: Allocator, new_size: Size) Allocator.Error!void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call ensureTotalCapacityContext instead.");
            return ensureTotalCapacityContext(self, allocator, new_size, undefined);
        }
        pub fn ensureTotalCapacityContext(self: *Self, allocator: Allocator, new_size: Size, ctx: Context) Allocator.Error!void {
            if (new_size > self.size)
                try self.growIfNeeded(allocator, new_size - self.size, ctx);
=======
        pub fn ensureTotalCapacity(self: *Self, allocator: Allocator, new_size: Size) Allocator.Error!void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call ensureTotalCapacityContext instead.");
            return ensureTotalCapacityContext(self, allocator, new_size, undefined);
        }
        pub fn ensureTotalCapacityContext(self: *Self, allocator: Allocator, new_size: Size, ctx: Context) Allocator.Error!void {
            self.pointer_stability.lock();
            defer self.pointer_stability.unlock();
            if (new_size > self.size)
                try self.growIfNeeded(allocator, new_size - self.size, ctx);
>>>>>>> theirs
        }

        pub fn ensureUnusedCapacity(self: *Self, additional_size: Size) Allocator.Error!void {
            return ensureTotalCapacity(self, self.count() + additional_size);
        }

        pub fn clearRetainingCapacity(self: *Self) void {
            self.pointer_stability.lock();
            defer self.pointer_stability.unlock();
            if (self.metadata) |_| {
                self.initMetadatas();
<<<<<<< ours
                self.header().size = 0;
||||||| base
                self.size = 0;
                self.available = @as(u32, @truncate((self.capacity() * max_load_percentage) / 100));
=======
                self.size = 0;
                self.available = @truncate((self.capacity() * max_load_percentage) / 100);
>>>>>>> theirs
            }
        }

<<<<<<< ours
        pub fn count(self: *const Self) Size {
            return self.header().size;
||||||| base
        pub fn clearAndFree(self: *Self, allocator: Allocator) void {
            self.deallocate(allocator);
            self.size = 0;
            self.available = 0;
        }

        pub fn count(self: *const Self) Size {
            return self.size;
=======
        pub fn clearAndFree(self: *Self, allocator: Allocator) void {
            self.pointer_stability.lock();
            defer self.pointer_stability.unlock();
            self.deallocate(allocator);
            self.size = 0;
            self.available = 0;
        }

        pub fn count(self: Self) Size {
            return self.size;
>>>>>>> theirs
        }

        fn header(self: Self) *Header {
            return @ptrCast(@as([*]Header, @ptrCast(@alignCast(self.metadata.?))) - 1);
        }

<<<<<<< ours
        fn keys(self: *const Self) [*]K {
            return self.header().keys.ptr(self.metadata.?);
||||||| base
        fn keys(self: *const Self) [*]K {
            return self.header().keys;
=======
        fn keys(self: Self) [*]K {
            return self.header().keys;
>>>>>>> theirs
        }

<<<<<<< ours
        fn values(self: *const Self) [*]V {
            return self.header().values.ptr(self.metadata.?);
||||||| base
        fn values(self: *const Self) [*]V {
            return self.header().values;
=======
        fn values(self: Self) [*]V {
            return self.header().values;
>>>>>>> theirs
        }

        pub fn capacity(self: Self) Size {
            if (self.metadata == null) return 0;

            return self.header().capacity;
        }

        pub fn iterator(self: *const Self) Iterator {
            return .{ .hm = self };
        }

        pub fn keyIterator(self: Self) KeyIterator {
            if (self.metadata) |metadata| {
                return .{
                    .len = self.capacity(),
                    .metadata = metadata,
                    .items = self.keys(),
                };
            } else {
                return .{
                    .len = 0,
                    .metadata = undefined,
                    .items = undefined,
                };
            }
        }

        pub fn valueIterator(self: Self) ValueIterator {
            if (self.metadata) |metadata| {
                return .{
                    .len = self.capacity(),
                    .metadata = metadata,
                    .items = self.values(),
                };
            } else {
                return .{
                    .len = 0,
                    .metadata = undefined,
                    .items = undefined,
                };
            }
        }

        /// Insert an entry in the map. Assumes it is not already present.
        pub fn putNoClobber(self: *Self, key: K, value: V) Allocator.Error!void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call putNoClobberContext instead.");
            return self.putNoClobberContext(key, value, undefined);
        }
<<<<<<< ours
        pub fn putNoClobberContext(self: *Self, key: K, value: V, ctx: Context) Allocator.Error!void {
            assert(!self.containsContext(key, ctx));
            try self.growIfNeeded(1);

||||||| base
        pub fn putNoClobberContext(self: *Self, allocator: Allocator, key: K, value: V, ctx: Context) Allocator.Error!void {
            assert(!self.containsContext(key, ctx));
            try self.growIfNeeded(allocator, 1, ctx);

=======
        pub fn putNoClobberContext(self: *Self, allocator: Allocator, key: K, value: V, ctx: Context) Allocator.Error!void {
            {
                self.pointer_stability.lock();
                defer self.pointer_stability.unlock();
                try self.growIfNeeded(allocator, 1, ctx);
            }
>>>>>>> theirs
            self.putAssumeCapacityNoClobberContext(key, value, ctx);
        }

        /// Asserts there is enough capacity to store the new key-value pair.
        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPutAssumeCapacity`.
        pub fn putAssumeCapacity(self: *Self, key: K, value: V) void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call putAssumeCapacityContext instead.");
            return self.putAssumeCapacityContext(key, value, undefined);
        }
        pub fn putAssumeCapacityContext(self: *Self, key: K, value: V, ctx: Context) void {
            const gop = self.getOrPutAssumeCapacityContext(key, ctx);
            gop.value_ptr.* = value;
        }

        /// Insert an entry in the map. Assumes it is not already present,
        /// and that no allocation is needed.
        pub fn putAssumeCapacityNoClobber(self: *Self, key: K, value: V) void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call putAssumeCapacityNoClobberContext instead.");
            return self.putAssumeCapacityNoClobberContext(key, value, undefined);
        }
        pub fn putAssumeCapacityNoClobberContext(self: *Self, key: K, value: V, ctx: Context) void {
            assert(!self.containsContext(key, ctx));

            const hash: Hash = ctx.hash(key);
            const mask = self.capacity() - 1;
            var idx: usize = @truncate(hash & mask);

            var metadata = self.metadata.? + idx;
            while (metadata[0].isUsed()) {
                idx = (idx + 1) & mask;
                metadata = self.metadata.? + idx;
            }

            const fingerprint = Metadata.takeFingerprint(hash);
            metadata[0].fill(fingerprint);
            self.keys()[idx] = key;
            self.values()[idx] = value;
            self.header().size += 1;
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        pub fn fetchPut(self: *Self, key: K, value: V) Allocator.Error!?KV {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call fetchPutContext instead.");
            return self.fetchPutContext(key, value, undefined);
        }
        pub fn fetchPutContext(self: *Self, key: K, value: V, ctx: Context) Allocator.Error!?KV {
            const gop = try self.getOrPutContext(key, ctx);
            var result: ?KV = null;
            if (gop.found_existing) {
                result = KV{
                    .key = gop.key_ptr.*,
                    .value = gop.value_ptr.*,
                };
            }
            gop.value_ptr.* = value;
            return result;
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        /// If insertion happens, asserts there is enough capacity without allocating.
        pub fn fetchPutAssumeCapacity(self: *Self, key: K, value: V) ?KV {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call fetchPutAssumeCapacityContext instead.");
            return self.fetchPutAssumeCapacityContext(key, value, undefined);
        }
        pub fn fetchPutAssumeCapacityContext(self: *Self, key: K, value: V, ctx: Context) ?KV {
            const gop = self.getOrPutAssumeCapacityContext(key, ctx);
            var result: ?KV = null;
            if (gop.found_existing) {
                result = KV{
                    .key = gop.key_ptr.*,
                    .value = gop.value_ptr.*,
                };
            }
            gop.value_ptr.* = value;
            return result;
        }

        /// If there is an `Entry` with a matching key, it is deleted from
        /// the hash map, and then returned from this function.
        pub fn fetchRemove(self: *Self, key: K) ?KV {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call fetchRemoveContext instead.");
            return self.fetchRemoveContext(key, undefined);
        }
        pub fn fetchRemoveContext(self: *Self, key: K, ctx: Context) ?KV {
            return self.fetchRemoveAdapted(key, ctx);
        }
        pub fn fetchRemoveAdapted(self: *Self, key: anytype, ctx: anytype) ?KV {
            if (self.getIndex(key, ctx)) |idx| {
                const old_key = &self.keys()[idx];
                const old_val = &self.values()[idx];
                const result = KV{
                    .key = old_key.*,
                    .value = old_val.*,
                };
                self.metadata.?[idx].remove();
                old_key.* = undefined;
                old_val.* = undefined;
                self.header().size -= 1;
                return result;
            }

            return null;
        }

        /// Find the index containing the data for the given key.
<<<<<<< ours
        /// Whether this function returns null is almost always
        /// branched on after this function returns, and this function
        /// returns null/not null from separate code paths.  We
        /// want the optimizer to remove that branch and instead directly
        /// fuse the basic blocks after the branch to the basic blocks
        /// from this function.  To encourage that, this function is
        /// marked as inline.
        inline fn getIndex(self: Self, key: anytype, ctx: anytype) ?usize {
            if (self.header().size == 0) {
||||||| base
        /// Whether this function returns null is almost always
        /// branched on after this function returns, and this function
        /// returns null/not null from separate code paths.  We
        /// want the optimizer to remove that branch and instead directly
        /// fuse the basic blocks after the branch to the basic blocks
        /// from this function.  To encourage that, this function is
        /// marked as inline.
        inline fn getIndex(self: Self, key: anytype, ctx: anytype) ?usize {
            comptime verifyContext(@TypeOf(ctx), @TypeOf(key), K, Hash, false);

            if (self.size == 0) {
=======
        fn getIndex(self: Self, key: anytype, ctx: anytype) ?usize {
            if (self.size == 0) {
                // We use cold instead of unlikely to force a jump to this case,
                // no matter the weight of the opposing side.
                @branchHint(.cold);
>>>>>>> theirs
                return null;
            }

            // If you get a compile error on this line, it means that your generic hash
            // function is invalid for these parameters.
<<<<<<< ours
            const hash = ctx.hash(key);
            if (@TypeOf(hash) != Hash) {
                @compileError("Context " ++ @typeName(@TypeOf(ctx)) ++ " has a generic hash function that returns the wrong type! " ++ @typeName(Hash) ++ " was expected, but found " ++ @typeName(@TypeOf(hash)));
            }
||||||| base
            const hash = ctx.hash(key);
            // verifyContext can't verify the return type of generic hash functions,
            // so we need to double-check it here.
            if (@TypeOf(hash) != Hash) {
                @compileError("Context " ++ @typeName(@TypeOf(ctx)) ++ " has a generic hash function that returns the wrong type! " ++ @typeName(Hash) ++ " was expected, but found " ++ @typeName(@TypeOf(hash)));
            }
=======
            const hash: Hash = ctx.hash(key);

>>>>>>> theirs
            const mask = self.capacity() - 1;
            const fingerprint = Metadata.takeFingerprint(hash);
            // Don't loop indefinitely when there are no empty slots.
            var limit = self.capacity();
            var idx = @as(usize, @truncate(hash & mask));

            var metadata = self.metadata.? + idx;
            while (!metadata[0].isFree() and limit != 0) {
                if (metadata[0].isUsed() and metadata[0].fingerprint == fingerprint) {
                    const test_key = &self.keys()[idx];

                    if (ctx.eql(key, test_key.*)) {
                        return idx;
                    }
                }

                limit -= 1;
                idx = (idx + 1) & mask;
                metadata = self.metadata.? + idx;
            }

            return null;
        }

        pub fn getEntry(self: Self, key: K) ?Entry {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getEntryContext instead.");
            return self.getEntryContext(key, undefined);
        }
        pub fn getEntryContext(self: Self, key: K, ctx: Context) ?Entry {
            return self.getEntryAdapted(key, ctx);
        }
        pub fn getEntryAdapted(self: Self, key: anytype, ctx: anytype) ?Entry {
            if (self.getIndex(key, ctx)) |idx| {
                return Entry{
                    .key_ptr = &self.keys()[idx],
                    .value_ptr = &self.values()[idx],
                };
            }
            return null;
        }

        /// Insert an entry if the associated key is not already present, otherwise update preexisting value.
        pub fn put(self: *Self, key: K, value: V) Allocator.Error!void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call putContext instead.");
            return self.putContext(key, value, undefined);
        }
        pub fn putContext(self: *Self, key: K, value: V, ctx: Context) Allocator.Error!void {
            const result = try self.getOrPutContext(key, ctx);
            result.value_ptr.* = value;
        }

        /// Get an optional pointer to the actual key associated with adapted key, if present.
        pub fn getKeyPtr(self: Self, key: K) ?*K {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getKeyPtrContext instead.");
            return self.getKeyPtrContext(key, undefined);
        }
        pub fn getKeyPtrContext(self: Self, key: K, ctx: Context) ?*K {
            return self.getKeyPtrAdapted(key, ctx);
        }
        pub fn getKeyPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*K {
            if (self.getIndex(key, ctx)) |idx| {
                return &self.keys()[idx];
            }
            return null;
        }

        /// Get a copy of the actual key associated with adapted key, if present.
        pub fn getKey(self: Self, key: K) ?K {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getKeyContext instead.");
            return self.getKeyContext(key, undefined);
        }
        pub fn getKeyContext(self: Self, key: K, ctx: Context) ?K {
            return self.getKeyAdapted(key, ctx);
        }
        pub fn getKeyAdapted(self: Self, key: anytype, ctx: anytype) ?K {
            if (self.getIndex(key, ctx)) |idx| {
                return self.keys()[idx];
            }
            return null;
        }

        /// Get an optional pointer to the value associated with key, if present.
        pub fn getPtr(self: Self, key: K) ?*V {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getPtrContext instead.");
            return self.getPtrContext(key, undefined);
        }
        pub fn getPtrContext(self: Self, key: K, ctx: Context) ?*V {
            return self.getPtrAdapted(key, ctx);
        }
        pub fn getPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*V {
            if (self.getIndex(key, ctx)) |idx| {
                return &self.values()[idx];
            }
            return null;
        }

        /// Get a copy of the value associated with key, if present.
        pub fn get(self: Self, key: K) ?V {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getContext instead.");
            return self.getContext(key, undefined);
        }
        pub fn getContext(self: Self, key: K, ctx: Context) ?V {
            return self.getAdapted(key, ctx);
        }
        pub fn getAdapted(self: Self, key: anytype, ctx: anytype) ?V {
            if (self.getIndex(key, ctx)) |idx| {
                return self.values()[idx];
            }
            return null;
        }

        pub fn getOrPut(self: *Self, key: K) Allocator.Error!GetOrPutResult {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getOrPutContext instead.");
            return self.getOrPutContext(key, undefined);
        }
        pub fn getOrPutContext(self: *Self, key: K, ctx: Context) Allocator.Error!GetOrPutResult {
            const gop = try self.getOrPutContextAdapted(key, ctx);
            if (!gop.found_existing) {
                gop.key_ptr.* = key;
            }
            return gop;
        }
        pub fn getOrPutAdapted(self: *Self, key: anytype, key_ctx: anytype) Allocator.Error!GetOrPutResult {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getOrPutContextAdapted instead.");
            return self.getOrPutContextAdapted(key, key_ctx);
        }
<<<<<<< ours
        pub fn getOrPutContextAdapted(self: *Self, key: anytype, key_ctx: anytype) Allocator.Error!GetOrPutResult {
            self.growIfNeeded(1) catch |err| {
                // If allocation fails, try to do the lookup anyway.
                // If we find an existing item, we can return it.
                // Otherwise return the error, we could not add another.
                const index = self.getIndex(key, key_ctx) orelse return err;
                return GetOrPutResult{
                    .key_ptr = &self.keys()[index],
                    .value_ptr = &self.values()[index],
                    .found_existing = true,
||||||| base
        pub fn getOrPutContextAdapted(self: *Self, allocator: Allocator, key: anytype, key_ctx: anytype, ctx: Context) Allocator.Error!GetOrPutResult {
            self.growIfNeeded(allocator, 1, ctx) catch |err| {
                // If allocation fails, try to do the lookup anyway.
                // If we find an existing item, we can return it.
                // Otherwise return the error, we could not add another.
                const index = self.getIndex(key, key_ctx) orelse return err;
                return GetOrPutResult{
                    .key_ptr = &self.keys()[index],
                    .value_ptr = &self.values()[index],
                    .found_existing = true,
=======
        pub fn getOrPutContextAdapted(self: *Self, allocator: Allocator, key: anytype, key_ctx: anytype, ctx: Context) Allocator.Error!GetOrPutResult {
            {
                self.pointer_stability.lock();
                defer self.pointer_stability.unlock();
                self.growIfNeeded(allocator, 1, ctx) catch |err| {
                    // If allocation fails, try to do the lookup anyway.
                    // If we find an existing item, we can return it.
                    // Otherwise return the error, we could not add another.
                    const index = self.getIndex(key, key_ctx) orelse return err;
                    return GetOrPutResult{
                        .key_ptr = &self.keys()[index],
                        .value_ptr = &self.values()[index],
                        .found_existing = true,
                    };
>>>>>>> theirs
                };
            }
            return self.getOrPutAssumeCapacityAdapted(key, key_ctx);
        }

        pub fn getOrPutAssumeCapacity(self: *Self, key: K) GetOrPutResult {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getOrPutAssumeCapacityContext instead.");
            return self.getOrPutAssumeCapacityContext(key, undefined);
        }
        pub fn getOrPutAssumeCapacityContext(self: *Self, key: K, ctx: Context) GetOrPutResult {
            const result = self.getOrPutAssumeCapacityAdapted(key, ctx);
            if (!result.found_existing) {
                result.key_ptr.* = key;
            }
            return result;
        }
        pub fn getOrPutAssumeCapacityAdapted(self: *Self, key: anytype, ctx: anytype) GetOrPutResult {
<<<<<<< ours
||||||| base
            comptime verifyContext(@TypeOf(ctx), @TypeOf(key), K, Hash, false);

=======

>>>>>>> theirs
            // If you get a compile error on this line, it means that your generic hash
            // function is invalid for these parameters.
            const hash: Hash = ctx.hash(key);

            const mask = self.capacity() - 1;
            const fingerprint = Metadata.takeFingerprint(hash);
            var limit = self.capacity();
            var idx = @as(usize, @truncate(hash & mask));

            var first_tombstone_idx: usize = self.capacity(); // invalid index
            var metadata = self.metadata.? + idx;
            while (!metadata[0].isFree() and limit != 0) {
                if (metadata[0].isUsed() and metadata[0].fingerprint == fingerprint) {
                    const test_key = &self.keys()[idx];
                    // If you get a compile error on this line, it means that your generic eql
                    // function is invalid for these parameters.

                    if (ctx.eql(key, test_key.*)) {
                        return GetOrPutResult{
                            .key_ptr = test_key,
                            .value_ptr = &self.values()[idx],
                            .found_existing = true,
                        };
                    }
                } else if (first_tombstone_idx == self.capacity() and metadata[0].isTombstone()) {
                    first_tombstone_idx = idx;
                }

                limit -= 1;
                idx = (idx + 1) & mask;
                metadata = self.metadata.? + idx;
            }

            if (first_tombstone_idx < self.capacity()) {
                // Cheap try to lower probing lengths after deletions. Recycle a tombstone.
                idx = first_tombstone_idx;
                metadata = self.metadata.? + idx;
            }

            metadata[0].fill(fingerprint);
            const new_key = &self.keys()[idx];
            const new_value = &self.values()[idx];
            new_key.* = undefined;
            new_value.* = undefined;
            self.header().size += 1;

            return GetOrPutResult{
                .key_ptr = new_key,
                .value_ptr = new_value,
                .found_existing = false,
            };
        }

        pub fn getOrPutValue(self: *Self, key: K, value: V) Allocator.Error!Entry {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getOrPutValueContext instead.");
            return self.getOrPutValueContext(key, value, undefined);
        }
        pub fn getOrPutValueContext(self: *Self, key: K, value: V, ctx: Context) Allocator.Error!Entry {
            const res = try self.getOrPutAdapted(key, ctx);
            if (!res.found_existing) {
                res.key_ptr.* = key;
                res.value_ptr.* = value;
            }
            return Entry{ .key_ptr = res.key_ptr, .value_ptr = res.value_ptr };
        }

        /// Return true if there is a value associated with key in the map.
        pub fn contains(self: Self, key: K) bool {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call containsContext instead.");
            return self.containsContext(key, undefined);
        }
        pub fn containsContext(self: Self, key: K, ctx: Context) bool {
            return self.containsAdapted(key, ctx);
        }
        pub fn containsAdapted(self: Self, key: anytype, ctx: anytype) bool {
            return self.getIndex(key, ctx) != null;
        }

        fn removeByIndex(self: *Self, idx: usize) void {
            self.metadata.?[idx].remove();
            self.keys()[idx] = undefined;
            self.values()[idx] = undefined;
            self.header().size -= 1;
        }

        /// If there is an `Entry` with a matching key, it is deleted from
        /// the hash map, and this function returns true.  Otherwise this
        /// function returns false.
        ///
        /// TODO: answer the question in these doc comments, does this
        /// increase the unused capacity by one?
        pub fn remove(self: *Self, key: K) bool {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call removeContext instead.");
            return self.removeContext(key, undefined);
        }

        /// TODO: answer the question in these doc comments, does this
        /// increase the unused capacity by one?
        pub fn removeContext(self: *Self, key: K, ctx: Context) bool {
            return self.removeAdapted(key, ctx);
        }

        /// TODO: answer the question in these doc comments, does this
        /// increase the unused capacity by one?
        pub fn removeAdapted(self: *Self, key: anytype, ctx: anytype) bool {
            if (self.getIndex(key, ctx)) |idx| {
                self.removeByIndex(idx);
                return true;
            }

            return false;
        }

        /// Delete the entry with key pointed to by key_ptr from the hash map.
        /// key_ptr is assumed to be a valid pointer to a key that is present
        /// in the hash map.
        ///
        /// TODO: answer the question in these doc comments, does this
        /// increase the unused capacity by one?
        pub fn removeByPtr(self: *Self, key_ptr: *K) void {
            // if @sizeOf(K) == 0 then there is at most one item in the hash
            // map, which is assumed to exist as key_ptr must be valid.  This
            // item must be at index 0.
            const idx = if (@sizeOf(K) > 0)
                (key_ptr - self.keys())
            else
                0;

            self.removeByIndex(idx);
        }

        fn initMetadatas(self: *Self) void {
            @memset(@as([*]u8, @ptrCast(self.metadata.?))[0 .. @sizeOf(Metadata) * self.capacity()], 0);
        }

<<<<<<< ours
        fn growIfNeeded(self: *Self, new_count: Size) Allocator.Error!void {
            const available = self.capacity() - self.header().size;
            if (new_count > available) return error.OutOfMemory;
||||||| base
        // This counts the number of occupied slots (not counting tombstones), which is
        // what has to stay under the max_load_percentage of capacity.
        fn load(self: *const Self) Size {
            const max_load = (self.capacity() * max_load_percentage) / 100;
            assert(max_load >= self.available);
            return @as(Size, @truncate(max_load - self.available));
        }

        fn growIfNeeded(self: *Self, allocator: Allocator, new_count: Size, ctx: Context) Allocator.Error!void {
            if (new_count > self.available) {
                try self.grow(allocator, capacityForSize(self.load() + new_count), ctx);
            }
=======
        // This counts the number of occupied slots (not counting tombstones), which is
        // what has to stay under the max_load_percentage of capacity.
        fn load(self: Self) Size {
            const max_load = (self.capacity() * max_load_percentage) / 100;
            assert(max_load >= self.available);
            return @as(Size, @truncate(max_load - self.available));
        }

        fn growIfNeeded(self: *Self, allocator: Allocator, new_count: Size, ctx: Context) Allocator.Error!void {
            if (new_count > self.available) {
                try self.grow(allocator, capacityForSize(self.load() + new_count), ctx);
            }
>>>>>>> theirs
        }

<<<<<<< ours
        /// The memory layout for the underlying buffer for a given capacity.
        const Layout = struct {
            /// The total size of the buffer required. The buffer is expected
            /// to be aligned to `base_align`.
            total_size: usize,
||||||| base
        pub fn clone(self: Self, allocator: Allocator) Allocator.Error!Self {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call cloneContext instead.");
            return self.cloneContext(allocator, @as(Context, undefined));
        }
        pub fn cloneContext(self: Self, allocator: Allocator, new_ctx: anytype) Allocator.Error!HashMapUnmanaged(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other = HashMapUnmanaged(K, V, @TypeOf(new_ctx), max_load_percentage){};
            if (self.size == 0)
                return other;

            const new_cap = capacityForSize(self.size);
            try other.allocate(allocator, new_cap);
            other.initMetadatas();
            other.available = @truncate((new_cap * max_load_percentage) / 100);

            var i: Size = 0;
            var metadata = self.metadata.?;
            const keys_ptr = self.keys();
            const values_ptr = self.values();
            while (i < self.capacity()) : (i += 1) {
                if (metadata[i].isUsed()) {
                    other.putAssumeCapacityNoClobberContext(keys_ptr[i], values_ptr[i], new_ctx);
                    if (other.size == self.size)
                        break;
                }
            }

            return other;
        }
=======
        pub fn clone(self: Self, allocator: Allocator) Allocator.Error!Self {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call cloneContext instead.");
            return self.cloneContext(allocator, @as(Context, undefined));
        }
        pub fn cloneContext(self: Self, allocator: Allocator, new_ctx: anytype) Allocator.Error!HashMapUnmanaged(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other: HashMapUnmanaged(K, V, @TypeOf(new_ctx), max_load_percentage) = .empty;
            if (self.size == 0)
                return other;

            const new_cap = capacityForSize(self.size);
            try other.allocate(allocator, new_cap);
            other.initMetadatas();
            other.available = @truncate((new_cap * max_load_percentage) / 100);

            var i: Size = 0;
            var metadata = self.metadata.?;
            const keys_ptr = self.keys();
            const values_ptr = self.values();
            while (i < self.capacity()) : (i += 1) {
                if (metadata[i].isUsed()) {
                    other.putAssumeCapacityNoClobberContext(keys_ptr[i], values_ptr[i], new_ctx);
                    if (other.size == self.size)
                        break;
                }
            }

            return other;
        }
>>>>>>> theirs

<<<<<<< ours
            /// The offset to the start of the keys data.
            keys_start: usize,
||||||| base
        /// Set the map to an empty state, making deinitialization a no-op, and
        /// returning a copy of the original.
        pub fn move(self: *Self) Self {
            const result = self.*;
            self.* = .{};
            return result;
        }
=======
        /// Set the map to an empty state, making deinitialization a no-op, and
        /// returning a copy of the original.
        pub fn move(self: *Self) Self {
            self.pointer_stability.assertUnlocked();
            const result = self.*;
            self.* = .empty;
            return result;
        }
>>>>>>> theirs

<<<<<<< ours
            /// The offset to the start of the values data.
            vals_start: usize,
||||||| base
        fn grow(self: *Self, allocator: Allocator, new_capacity: Size, ctx: Context) Allocator.Error!void {
            @setCold(true);
            const new_cap = @max(new_capacity, minimal_capacity);
            assert(new_cap > self.capacity());
            assert(std.math.isPowerOfTwo(new_cap));
=======
        /// Rehash the map, in-place.
        ///
        /// Over time, due to the current tombstone-based implementation, a
        /// HashMap could become fragmented due to the buildup of tombstone
        /// entries that causes a performance degradation due to excessive
        /// probing. The kind of pattern that might cause this is a long-lived
        /// HashMap with repeated inserts and deletes.
        ///
        /// After this function is called, there will be no tombstones in
        /// the HashMap, each of the entries is rehashed and any existing
        /// key/value pointers into the HashMap are invalidated.
        pub fn rehash(self: *Self, ctx: anytype) void {
            const mask = self.capacity() - 1;

            var metadata = self.metadata.?;
            var keys_ptr = self.keys();
            var values_ptr = self.values();
            var curr: Size = 0;

            // While we are re-hashing every slot, we will use the
            // fingerprint to mark used buckets as being used and either free
            // (needing to be rehashed) or tombstone (already rehashed).

            while (curr < self.capacity()) : (curr += 1) {
                metadata[curr].fingerprint = Metadata.free;
            }

            // Now iterate over all the buckets, rehashing them

            curr = 0;
            while (curr < self.capacity()) {
                if (!metadata[curr].isUsed()) {
                    assert(metadata[curr].isFree());
                    curr += 1;
                    continue;
                }

                const hash = ctx.hash(keys_ptr[curr]);
                const fingerprint = Metadata.takeFingerprint(hash);
                var idx = @as(usize, @truncate(hash & mask));

                // For each bucket, rehash to an index:
                // 1) before the cursor, probed into a free slot, or
                // 2) equal to the cursor, no need to move, or
                // 3) ahead of the cursor, probing over already rehashed

                while ((idx < curr and metadata[idx].isUsed()) or
                    (idx > curr and metadata[idx].fingerprint == Metadata.tombstone))
                {
                    idx = (idx + 1) & mask;
                }

                if (idx < curr) {
                    assert(metadata[idx].isFree());
                    metadata[idx].fill(fingerprint);
                    keys_ptr[idx] = keys_ptr[curr];
                    values_ptr[idx] = values_ptr[curr];

                    metadata[curr].used = 0;
                    assert(metadata[curr].isFree());
                    keys_ptr[curr] = undefined;
                    values_ptr[curr] = undefined;

                    curr += 1;
                } else if (idx == curr) {
                    metadata[idx].fingerprint = fingerprint;
                    curr += 1;
                } else {
                    assert(metadata[idx].fingerprint != Metadata.tombstone);
                    metadata[idx].fingerprint = Metadata.tombstone;
                    if (metadata[idx].isUsed()) {
                        std.mem.swap(K, &keys_ptr[curr], &keys_ptr[idx]);
                        std.mem.swap(V, &values_ptr[curr], &values_ptr[idx]);
                    } else {
                        metadata[idx].used = 1;
                        keys_ptr[idx] = keys_ptr[curr];
                        values_ptr[idx] = values_ptr[curr];

                        metadata[curr].fingerprint = Metadata.free;
                        metadata[curr].used = 0;
                        keys_ptr[curr] = undefined;
                        values_ptr[curr] = undefined;

                        curr += 1;
                    }
                }
            }
        }

        fn grow(self: *Self, allocator: Allocator, new_capacity: Size, ctx: Context) Allocator.Error!void {
            @branchHint(.cold);
            const new_cap = @max(new_capacity, minimal_capacity);
            assert(new_cap > self.capacity());
            assert(std.math.isPowerOfTwo(new_cap));
>>>>>>> theirs

<<<<<<< ours
            /// The capacity that was used to calculate this layout.
            capacity: Size,
        };
||||||| base
            var map = Self{};
            defer map.deinit(allocator);
            try map.allocate(allocator, new_cap);
            map.initMetadatas();
            map.available = @truncate((new_cap * max_load_percentage) / 100);

            if (self.size != 0) {
                const old_capacity = self.capacity();
                var i: Size = 0;
                var metadata = self.metadata.?;
                const keys_ptr = self.keys();
                const values_ptr = self.values();
                while (i < old_capacity) : (i += 1) {
                    if (metadata[i].isUsed()) {
                        map.putAssumeCapacityNoClobberContext(keys_ptr[i], values_ptr[i], ctx);
                        if (map.size == self.size)
                            break;
                    }
                }
            }

            self.size = 0;
            std.mem.swap(Self, self, &map);
        }

        fn allocate(self: *Self, allocator: Allocator, new_capacity: Size) Allocator.Error!void {
            const header_align = @alignOf(Header);
            const key_align = if (@sizeOf(K) == 0) 1 else @alignOf(K);
            const val_align = if (@sizeOf(V) == 0) 1 else @alignOf(V);
            const max_align = comptime @max(header_align, key_align, val_align);

            const meta_size = @sizeOf(Header) + new_capacity * @sizeOf(Metadata);
            comptime assert(@alignOf(Metadata) == 1);
=======
            var map: Self = .{};
            try map.allocate(allocator, new_cap);
            errdefer comptime unreachable;
            map.pointer_stability.lock();
            map.initMetadatas();
            map.available = @truncate((new_cap * max_load_percentage) / 100);

            if (self.size != 0) {
                const old_capacity = self.capacity();
                for (
                    self.metadata.?[0..old_capacity],
                    self.keys()[0..old_capacity],
                    self.values()[0..old_capacity],
                ) |m, k, v| {
                    if (!m.isUsed()) continue;
                    map.putAssumeCapacityNoClobberContext(k, v, ctx);
                    if (map.size == self.size) break;
                }
            }

            self.size = 0;
            self.pointer_stability = .{};
            std.mem.swap(Self, self, &map);
            map.deinit(allocator);
        }

        fn allocate(self: *Self, allocator: Allocator, new_capacity: Size) Allocator.Error!void {
            const header_align = @alignOf(Header);
            const key_align = if (@sizeOf(K) == 0) 1 else @alignOf(K);
            const val_align = if (@sizeOf(V) == 0) 1 else @alignOf(V);
            const max_align: Alignment = comptime .fromByteUnits(@max(header_align, key_align, val_align));

            const new_cap: usize = new_capacity;
            const meta_size = @sizeOf(Header) + new_cap * @sizeOf(Metadata);
            comptime assert(@alignOf(Metadata) == 1);
>>>>>>> theirs

<<<<<<< ours
        /// Returns the memory layout for the buffer for a given capacity.
        /// The actual size may be able to fit more than the given capacity
        /// because capacity is rounded up to the next power of two. This is
        /// a design requirement for this hash map implementation.
        pub fn layoutForCapacity(new_capacity: Size) Layout {
            assert(new_capacity == 0 or std.math.isPowerOfTwo(new_capacity));

            // Pack our metadata, keys, and values.
            const meta_start = @sizeOf(Header);
            const meta_end = @sizeOf(Header) + new_capacity * @sizeOf(Metadata);
            const keys_start = std.mem.alignForward(usize, meta_end, key_align);
            const keys_end = keys_start + new_capacity * @sizeOf(K);
||||||| base
            const keys_start = std.mem.alignForward(usize, meta_size, key_align);
            const keys_end = keys_start + new_capacity * @sizeOf(K);

=======
            const keys_start = std.mem.alignForward(usize, meta_size, key_align);
            const keys_end = keys_start + new_cap * @sizeOf(K);

>>>>>>> theirs
            const vals_start = std.mem.alignForward(usize, keys_end, val_align);
            const vals_end = vals_start + new_cap * @sizeOf(V);

<<<<<<< ours
            // Our total memory size required is the end of our values
            // aligned to the base required alignment.
            const total_size = std.mem.alignForward(
                usize,
                vals_end,
                base_align.toByteUnits(),
            );
||||||| base
            const total_size = std.mem.alignForward(usize, vals_end, max_align);

            const slice = try allocator.alignedAlloc(u8, max_align, total_size);
            const ptr = @intFromPtr(slice.ptr);

            const metadata = ptr + @sizeOf(Header);

            const hdr = @as(*Header, @ptrFromInt(ptr));
            if (@sizeOf([*]V) != 0) {
                hdr.values = @as([*]V, @ptrFromInt(ptr + vals_start));
            }
            if (@sizeOf([*]K) != 0) {
                hdr.keys = @as([*]K, @ptrFromInt(ptr + keys_start));
            }
            hdr.capacity = new_capacity;
            self.metadata = @as([*]Metadata, @ptrFromInt(metadata));
        }

        fn deallocate(self: *Self, allocator: Allocator) void {
            if (self.metadata == null) return;

            const header_align = @alignOf(Header);
            const key_align = if (@sizeOf(K) == 0) 1 else @alignOf(K);
            const val_align = if (@sizeOf(V) == 0) 1 else @alignOf(V);
            const max_align = comptime @max(header_align, key_align, val_align);

            const cap = self.capacity();
            const meta_size = @sizeOf(Header) + cap * @sizeOf(Metadata);
            comptime assert(@alignOf(Metadata) == 1);

            const keys_start = std.mem.alignForward(usize, meta_size, key_align);
            const keys_end = keys_start + cap * @sizeOf(K);
=======
            const total_size = max_align.forward(vals_end);

            const slice = try allocator.alignedAlloc(u8, max_align, total_size);
            const ptr: [*]u8 = @ptrCast(slice.ptr);

            const metadata = ptr + @sizeOf(Header);

            const hdr = @as(*Header, @ptrCast(@alignCast(ptr)));
            if (@sizeOf([*]V) != 0) {
                hdr.values = @ptrCast(@alignCast((ptr + vals_start)));
            }
            if (@sizeOf([*]K) != 0) {
                hdr.keys = @ptrCast(@alignCast((ptr + keys_start)));
            }
            hdr.capacity = new_capacity;
            self.metadata = @ptrCast(@alignCast(metadata));
        }

        fn deallocate(self: *Self, allocator: Allocator) void {
            if (self.metadata == null) return;

            const header_align = @alignOf(Header);
            const key_align = if (@sizeOf(K) == 0) 1 else @alignOf(K);
            const val_align = if (@sizeOf(V) == 0) 1 else @alignOf(V);
            const max_align = comptime @max(header_align, key_align, val_align);

            const cap: usize = self.capacity();
            const meta_size = @sizeOf(Header) + cap * @sizeOf(Metadata);
            comptime assert(@alignOf(Metadata) == 1);

            const keys_start = std.mem.alignForward(usize, meta_size, key_align);
            const keys_end = keys_start + cap * @sizeOf(K);
>>>>>>> theirs

<<<<<<< ours
            // The offsets we actually store in the map are from the
            // metadata pointer so that we can use self.metadata as
            // the base.
            const keys_offset = keys_start - meta_start;
            const vals_offset = vals_start - meta_start;
||||||| base
            const vals_start = std.mem.alignForward(usize, keys_end, val_align);
            const vals_end = vals_start + cap * @sizeOf(V);

            const total_size = std.mem.alignForward(usize, vals_end, max_align);

            const slice = @as([*]align(max_align) u8, @ptrFromInt(@intFromPtr(self.header())))[0..total_size];
            allocator.free(slice);
=======
            const vals_start = std.mem.alignForward(usize, keys_end, val_align);
            const vals_end = vals_start + cap * @sizeOf(V);

            const total_size = std.mem.alignForward(usize, vals_end, max_align);

            const slice = @as([*]align(max_align) u8, @ptrCast(@alignCast(self.header())))[0..total_size];
            allocator.free(slice);
>>>>>>> theirs

<<<<<<< ours
            return .{
                .total_size = total_size,
                .keys_start = keys_offset,
                .vals_start = vals_offset,
                .capacity = new_capacity,
||||||| base
            self.metadata = null;
            self.available = 0;
        }

        /// This function is used in the debugger pretty formatters in tools/ to fetch the
        /// header type to facilitate fancy debug printing for this type.
        fn dbHelper(self: *Self, hdr: *Header, entry: *Entry) void {
            _ = self;
            _ = hdr;
            _ = entry;
        }

        comptime {
            if (builtin.mode == .Debug) {
                _ = &dbHelper;
            }
=======
            self.metadata = null;
            self.available = 0;
        }

        /// This function is used in the debugger pretty formatters in tools/ to fetch the
        /// header type to facilitate fancy debug printing for this type.
        fn dbHelper(self: *Self, hdr: *Header, entry: *Entry) void {
            _ = self;
            _ = hdr;
            _ = entry;
        }

        comptime {
            if (!builtin.strip_debug_info) _ = switch (builtin.zig_backend) {
                .stage2_llvm => &dbHelper,
                .stage2_x86_64 => KV,
                else => {},
>>>>>>> theirs
            };
        }
    };
}

const testing = std.testing;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

<<<<<<< ours
test "HashMap basic usage" {
    const Map = AutoHashMapUnmanaged(u32, u32);

    const alloc = testing.allocator;
    const cap = 16;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);

    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map basic usage" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "basic usage" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    const count = 5;
    var i: u32 = 0;
    var total: u32 = 0;
    while (i < count) : (i += 1) {
        try map.put(i, i);
        total += i;
    }

    var sum: u32 = 0;
    var it = map.iterator();
    while (it.next()) |kv| {
        sum += kv.key_ptr.*;
    }
    try expectEqual(total, sum);

    i = 0;
    sum = 0;
    while (i < count) : (i += 1) {
        try expectEqual(i, map.get(i).?);
        sum += map.get(i).?;
    }
    try expectEqual(total, sum);
}

<<<<<<< ours
test "HashMap ensureTotalCapacity" {
    const Map = AutoHashMapUnmanaged(i32, i32);
    const cap = 32;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map ensureTotalCapacity" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();
=======
test "ensureTotalCapacity" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    const initial_capacity = map.capacity();
    try testing.expect(initial_capacity >= 20);
    var i: i32 = 0;
    while (i < 20) : (i += 1) {
        try testing.expect(map.fetchPutAssumeCapacity(i, i + 10) == null);
    }
    // shouldn't resize from putAssumeCapacity
    try testing.expect(initial_capacity == map.capacity());
}

<<<<<<< ours
test "HashMap ensureUnusedCapacity with tombstones" {
    const Map = AutoHashMapUnmanaged(i32, i32);
    const cap = 32;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map ensureUnusedCapacity with tombstones" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();
=======
test "ensureUnusedCapacity with tombstones" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    var i: i32 = 0;
    while (i < 100) : (i += 1) {
        try map.ensureUnusedCapacity(1);
        map.putAssumeCapacity(i, i);
        _ = map.remove(i);
    }
}

<<<<<<< ours
test "HashMap clearRetainingCapacity" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 16;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map clearRetainingCapacity" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "clearRetainingCapacity" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    map.clearRetainingCapacity();

    try map.put(1, 1);
    try expectEqual(map.get(1).?, 1);
    try expectEqual(map.count(), 1);

    map.clearRetainingCapacity();
    map.putAssumeCapacity(1, 1);
    try expectEqual(map.get(1).?, 1);
    try expectEqual(map.count(), 1);

    const actual_cap = map.capacity();
    try expect(actual_cap > 0);

    map.clearRetainingCapacity();
    map.clearRetainingCapacity();
    try expectEqual(map.count(), 0);
    try expectEqual(map.capacity(), actual_cap);
    try expect(!map.contains(1));
}

<<<<<<< ours
test "HashMap ensureTotalCapacity with existing elements" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = Map.minimal_capacity;
||||||| base
test "std.hash_map grow" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    const growTo = 12456;

    var i: u32 = 0;
    while (i < growTo) : (i += 1) {
        try map.put(i, i);
    }
    try expectEqual(map.count(), growTo);

    i = 0;
    var it = map.iterator();
    while (it.next()) |kv| {
        try expectEqual(kv.key_ptr.*, kv.value_ptr.*);
        i += 1;
    }
    try expectEqual(i, growTo);

    i = 0;
    while (i < growTo) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }
}

test "std.hash_map clone" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var a = try map.clone();
    defer a.deinit();

    try expectEqual(a.count(), 0);

    try a.put(1, 1);
    try a.put(2, 2);
    try a.put(3, 3);

    var b = try a.clone();
    defer b.deinit();

    try expectEqual(b.count(), 3);
    try expectEqual(b.get(1).?, 1);
    try expectEqual(b.get(2).?, 2);
    try expectEqual(b.get(3).?, 3);

    var original = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer original.deinit();

    var i: u8 = 0;
    while (i < 10) : (i += 1) {
        try original.putNoClobber(i, i * 10);
    }

    var copy = try original.clone();
    defer copy.deinit();

    i = 0;
    while (i < 10) : (i += 1) {
        try testing.expect(copy.get(i).? == i * 10);
    }
}
=======
test "grow" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    const growTo = 12456;

    var i: u32 = 0;
    while (i < growTo) : (i += 1) {
        try map.put(i, i);
    }
    try expectEqual(map.count(), growTo);

    i = 0;
    var it = map.iterator();
    while (it.next()) |kv| {
        try expectEqual(kv.key_ptr.*, kv.value_ptr.*);
        i += 1;
    }
    try expectEqual(i, growTo);

    i = 0;
    while (i < growTo) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }
}

test "clone" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var a = try map.clone();
    defer a.deinit();

    try expectEqual(a.count(), 0);

    try a.put(1, 1);
    try a.put(2, 2);
    try a.put(3, 3);

    var b = try a.clone();
    defer b.deinit();

    try expectEqual(b.count(), 3);
    try expectEqual(b.get(1).?, 1);
    try expectEqual(b.get(2).?, 2);
    try expectEqual(b.get(3).?, 3);

    var original = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer original.deinit();

    var i: u8 = 0;
    while (i < 10) : (i += 1) {
        try original.putNoClobber(i, i * 10);
    }

    var copy = try original.clone();
    defer copy.deinit();

    i = 0;
    while (i < 10) : (i += 1) {
        try testing.expect(copy.get(i).? == i * 10);
    }
}
>>>>>>> theirs

<<<<<<< ours
    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map ensureTotalCapacity with existing elements" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "ensureTotalCapacity with existing elements" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    try map.put(0, 0);
    try expectEqual(map.count(), 1);
    try expectEqual(map.capacity(), Map.minimal_capacity);

    try testing.expectError(error.OutOfMemory, map.ensureTotalCapacity(65));
    try expectEqual(map.count(), 1);
    try expectEqual(map.capacity(), Map.minimal_capacity);
}

<<<<<<< ours
test "HashMap remove" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 32;
||||||| base
test "std.hash_map ensureTotalCapacity satisfies max load factor" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    try map.ensureTotalCapacity(127);
    try expectEqual(map.capacity(), 256);
}
=======
test "ensureTotalCapacity satisfies max load factor" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    try map.ensureTotalCapacity(127);
    try expectEqual(map.capacity(), 256);
}
>>>>>>> theirs

<<<<<<< ours
    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map remove" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "remove" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        if (i % 3 == 0) {
            _ = map.remove(i);
        }
    }
    try expectEqual(map.count(), 10);
    var it = map.iterator();
    while (it.next()) |kv| {
        try expectEqual(kv.key_ptr.*, kv.value_ptr.*);
        try expect(kv.key_ptr.* % 3 != 0);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        if (i % 3 == 0) {
            try expect(!map.contains(i));
        } else {
            try expectEqual(map.get(i).?, i);
        }
    }
}

<<<<<<< ours
test "HashMap reverse removes" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 32;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map reverse removes" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "reverse removes" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.putNoClobber(i, i);
    }

    i = 16;
    while (i > 0) : (i -= 1) {
        _ = map.remove(i - 1);
        try expect(!map.contains(i - 1));
        var j: u32 = 0;
        while (j < i - 1) : (j += 1) {
            try expectEqual(map.get(j).?, j);
        }
    }

    try expectEqual(map.count(), 0);
}

<<<<<<< ours
test "HashMap multiple removes on same metadata" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 32;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map multiple removes on same metadata" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "multiple removes on same metadata" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    _ = map.remove(7);
    _ = map.remove(15);
    _ = map.remove(14);
    _ = map.remove(13);
    try expect(!map.contains(7));
    try expect(!map.contains(15));
    try expect(!map.contains(14));
    try expect(!map.contains(13));

    i = 0;
    while (i < 13) : (i += 1) {
        if (i == 7) {
            try expect(!map.contains(i));
        } else {
            try expectEqual(map.get(i).?, i);
        }
    }

    try map.put(15, 15);
    try map.put(13, 13);
    try map.put(14, 14);
    try map.put(7, 7);
    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }
}

<<<<<<< ours
test "HashMap put and remove loop in random order" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 64;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map put and remove loop in random order" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "put and remove loop in random order" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

<<<<<<< ours
    var keys: std.ArrayList(u32) = .empty;
    defer keys.deinit(alloc);
||||||| base
    var keys = std.ArrayList(u32).init(std.testing.allocator);
    defer keys.deinit();
=======
    var keys = std.array_list.Managed(u32).init(std.testing.allocator);
    defer keys.deinit();
>>>>>>> theirs

    const size = 32;
    const iterations = 100;

    var i: u32 = 0;
    while (i < size) : (i += 1) {
        try keys.append(alloc, i);
    }
    var prng = std.Random.DefaultPrng.init(std.testing.random_seed);
    const random = prng.random();

    while (i < iterations) : (i += 1) {
        random.shuffle(u32, keys.items);

        for (keys.items) |key| {
            try map.put(key, key);
        }
        try expectEqual(map.count(), size);

        for (keys.items) |key| {
            _ = map.remove(key);
        }
        try expectEqual(map.count(), 0);
    }
}

<<<<<<< ours
test "HashMap put" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 32;
||||||| base
test "std.hash_map remove one million elements in random order" {
    const Map = AutoHashMap(u32, u32);
    const n = 1000 * 1000;
    var map = Map.init(std.heap.page_allocator);
    defer map.deinit();
=======
test "remove many elements in random order" {
    const Map = AutoHashMap(u32, u32);
    const n = 1000 * 100;
    var map = Map.init(std.heap.page_allocator);
    defer map.deinit();
>>>>>>> theirs

<<<<<<< ours
    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
    var keys = std.ArrayList(u32).init(std.heap.page_allocator);
    defer keys.deinit();

    var i: u32 = 0;
    while (i < n) : (i += 1) {
        keys.append(i) catch unreachable;
    }

    var prng = std.Random.DefaultPrng.init(0);
    const random = prng.random();
    random.shuffle(u32, keys.items);

    for (keys.items) |key| {
        map.put(key, key) catch unreachable;
    }

    random.shuffle(u32, keys.items);
    i = 0;
    while (i < n) : (i += 1) {
        const key = keys.items[i];
        _ = map.remove(key);
    }
}

test "std.hash_map put" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
    var keys = std.array_list.Managed(u32).init(std.heap.page_allocator);
    defer keys.deinit();

    var i: u32 = 0;
    while (i < n) : (i += 1) {
        keys.append(i) catch unreachable;
    }

    var prng = std.Random.DefaultPrng.init(std.testing.random_seed);
    const random = prng.random();
    random.shuffle(u32, keys.items);

    for (keys.items) |key| {
        map.put(key, key) catch unreachable;
    }

    random.shuffle(u32, keys.items);
    i = 0;
    while (i < n) : (i += 1) {
        const key = keys.items[i];
        _ = map.remove(key);
    }
}

test "put" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i * 16 + 1);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i * 16 + 1);
    }
}

<<<<<<< ours
test "HashMap put full load" {
    const Map = AutoHashMapUnmanaged(usize, usize);
    const cap = 16;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);

    for (0..cap) |i| try map.put(i, i);
    for (0..cap) |i| try expectEqual(map.get(i).?, i);

    try testing.expectError(error.OutOfMemory, map.put(cap, cap));
}

test "HashMap putAssumeCapacity" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 32;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map putAssumeCapacity" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "putAssumeCapacity" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    var i: u32 = 0;
    while (i < 20) : (i += 1) {
        map.putAssumeCapacityNoClobber(i, i);
    }

    i = 0;
    var sum = i;
    while (i < 20) : (i += 1) {
        sum += map.getPtr(i).?.*;
    }
    try expectEqual(sum, 190);

    i = 0;
    while (i < 20) : (i += 1) {
        map.putAssumeCapacity(i, 1);
    }

    i = 0;
    sum = i;
    while (i < 20) : (i += 1) {
        sum += map.get(i).?;
    }
    try expectEqual(sum, 20);
}

<<<<<<< ours
test "HashMap repeat putAssumeCapacity/remove" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 32;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map repeat putAssumeCapacity/remove" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "repeat putAssumeCapacity/remove" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    const limit = cap;

    var i: u32 = 0;
    while (i < limit) : (i += 1) {
        map.putAssumeCapacityNoClobber(i, i);
    }

    // Repeatedly delete/insert an entry without resizing the map.
    // Put to different keys so entries don't land in the just-freed slot.
    i = 0;
    while (i < 10 * limit) : (i += 1) {
        try testing.expect(map.remove(i));
        if (i % 2 == 0) {
            map.putAssumeCapacityNoClobber(limit + i, i);
        } else {
            map.putAssumeCapacity(limit + i, i);
        }
    }

    i = 9 * limit;
    while (i < 10 * limit) : (i += 1) {
        try expectEqual(map.get(limit + i), i);
    }
    try expectEqual(map.count(), limit);
}

<<<<<<< ours
test "HashMap getOrPut" {
    const Map = AutoHashMapUnmanaged(u32, u32);
    const cap = 32;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map getOrPut" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
=======
test "getOrPut" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    var i: u32 = 0;
    while (i < 10) : (i += 1) {
        try map.put(i * 2, 2);
    }

    i = 0;
    while (i < 20) : (i += 1) {
        _ = try map.getOrPutValue(i, 1);
    }

    i = 0;
    var sum = i;
    while (i < 20) : (i += 1) {
        sum += map.get(i).?;
    }

    try expectEqual(sum, 30);
}

<<<<<<< ours
test "HashMap basic hash map usage" {
    const Map = AutoHashMapUnmanaged(i32, i32);
    const cap = 32;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map basic hash map usage" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();
=======
test "basic hash map usage" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    try testing.expect((try map.fetchPut(1, 11)) == null);
    try testing.expect((try map.fetchPut(2, 22)) == null);
    try testing.expect((try map.fetchPut(3, 33)) == null);
    try testing.expect((try map.fetchPut(4, 44)) == null);

    try map.putNoClobber(5, 55);
    try testing.expect((try map.fetchPut(5, 66)).?.value == 55);
    try testing.expect((try map.fetchPut(5, 55)).?.value == 66);

    const gop1 = try map.getOrPut(5);
    try testing.expect(gop1.found_existing == true);
    try testing.expect(gop1.value_ptr.* == 55);
    gop1.value_ptr.* = 77;
    try testing.expect(map.getEntry(5).?.value_ptr.* == 77);

    const gop2 = try map.getOrPut(99);
    try testing.expect(gop2.found_existing == false);
    gop2.value_ptr.* = 42;
    try testing.expect(map.getEntry(99).?.value_ptr.* == 42);

    const gop3 = try map.getOrPutValue(5, 5);
    try testing.expect(gop3.value_ptr.* == 77);

    const gop4 = try map.getOrPutValue(100, 41);
    try testing.expect(gop4.value_ptr.* == 41);

    try testing.expect(map.contains(2));
    try testing.expect(map.getEntry(2).?.value_ptr.* == 22);
    try testing.expect(map.get(2).? == 22);

    const rmv1 = map.fetchRemove(2);
    try testing.expect(rmv1.?.key == 2);
    try testing.expect(rmv1.?.value == 22);
    try testing.expect(map.fetchRemove(2) == null);
    try testing.expect(map.remove(2) == false);
    try testing.expect(map.getEntry(2) == null);
    try testing.expect(map.get(2) == null);

    try testing.expect(map.remove(3) == true);
}

<<<<<<< ours
test "HashMap ensureUnusedCapacity" {
    const Map = AutoHashMapUnmanaged(u64, u64);
    const cap = 64;
||||||| base
test "std.hash_map getOrPutAdapted" {
    const AdaptedContext = struct {
        fn eql(self: @This(), adapted_key: []const u8, test_key: u64) bool {
            _ = self;
            return std.fmt.parseInt(u64, adapted_key, 10) catch unreachable == test_key;
        }
        fn hash(self: @This(), adapted_key: []const u8) u64 {
            _ = self;
            const key = std.fmt.parseInt(u64, adapted_key, 10) catch unreachable;
            return (AutoContext(u64){}).hash(key);
        }
    };
    var map = AutoHashMap(u64, u64).init(testing.allocator);
    defer map.deinit();

    const keys = [_][]const u8{
        "1231",
        "4564",
        "7894",
        "1132",
        "65235",
        "95462",
        "0112305",
        "00658",
        "0",
        "2",
    };

    var real_keys: [keys.len]u64 = undefined;

    inline for (keys, 0..) |key_str, i| {
        const result = try map.getOrPutAdapted(key_str, AdaptedContext{});
        try testing.expect(!result.found_existing);
        real_keys[i] = std.fmt.parseInt(u64, key_str, 10) catch unreachable;
        result.key_ptr.* = real_keys[i];
        result.value_ptr.* = i * 2;
    }

    try testing.expectEqual(map.count(), keys.len);
=======
test "getOrPutAdapted" {
    const AdaptedContext = struct {
        fn eql(self: @This(), adapted_key: []const u8, test_key: u64) bool {
            _ = self;
            return std.fmt.parseInt(u64, adapted_key, 10) catch unreachable == test_key;
        }
        fn hash(self: @This(), adapted_key: []const u8) u64 {
            _ = self;
            const key = std.fmt.parseInt(u64, adapted_key, 10) catch unreachable;
            return (AutoContext(u64){}).hash(key);
        }
    };
    var map = AutoHashMap(u64, u64).init(testing.allocator);
    defer map.deinit();

    const keys = [_][]const u8{
        "1231",
        "4564",
        "7894",
        "1132",
        "65235",
        "95462",
        "0112305",
        "00658",
        "0",
        "2",
    };

    var real_keys: [keys.len]u64 = undefined;

    inline for (keys, 0..) |key_str, i| {
        const result = try map.getOrPutAdapted(key_str, AdaptedContext{});
        try testing.expect(!result.found_existing);
        real_keys[i] = std.fmt.parseInt(u64, key_str, 10) catch unreachable;
        result.key_ptr.* = real_keys[i];
        result.value_ptr.* = i * 2;
    }

    try testing.expectEqual(map.count(), keys.len);
>>>>>>> theirs

<<<<<<< ours
    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
    inline for (keys, 0..) |key_str, i| {
        const result = map.getOrPutAssumeCapacityAdapted(key_str, AdaptedContext{});
        try testing.expect(result.found_existing);
        try testing.expectEqual(real_keys[i], result.key_ptr.*);
        try testing.expectEqual(@as(u64, i) * 2, result.value_ptr.*);
        try testing.expectEqual(real_keys[i], map.getKeyAdapted(key_str, AdaptedContext{}).?);
    }
}

test "std.hash_map ensureUnusedCapacity" {
    var map = AutoHashMap(u64, u64).init(testing.allocator);
    defer map.deinit();
=======
    inline for (keys, 0..) |key_str, i| {
        const result = map.getOrPutAssumeCapacityAdapted(key_str, AdaptedContext{});
        try testing.expect(result.found_existing);
        try testing.expectEqual(real_keys[i], result.key_ptr.*);
        try testing.expectEqual(@as(u64, i) * 2, result.value_ptr.*);
        try testing.expectEqual(real_keys[i], map.getKeyAdapted(key_str, AdaptedContext{}).?);
    }
}

test "ensureUnusedCapacity" {
    var map = AutoHashMap(u64, u64).init(testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    try map.ensureUnusedCapacity(32);
    try testing.expectError(error.OutOfMemory, map.ensureUnusedCapacity(cap + 1));
}

<<<<<<< ours
test "HashMap removeByPtr" {
    const Map = AutoHashMapUnmanaged(i32, u64);
    const cap = 64;
||||||| base
test "std.hash_map removeByPtr" {
    var map = AutoHashMap(i32, u64).init(testing.allocator);
    defer map.deinit();
=======
test "removeByPtr" {
    var map = AutoHashMap(i32, u64).init(testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);

    var i: i32 = undefined;
    i = 0;
    while (i < 10) : (i += 1) {
        try map.put(i, 0);
    }

    try testing.expect(map.count() == 10);

    i = 0;
    while (i < 10) : (i += 1) {
        const key_ptr = map.getKeyPtr(i);
        try testing.expect(key_ptr != null);

        if (key_ptr) |ptr| {
            map.removeByPtr(ptr);
        }
    }

    try testing.expect(map.count() == 0);
}

<<<<<<< ours
test "HashMap removeByPtr 0 sized key" {
    const Map = AutoHashMapUnmanaged(i32, u64);
    const cap = 64;

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);
||||||| base
test "std.hash_map removeByPtr 0 sized key" {
    var map = AutoHashMap(u0, u64).init(testing.allocator);
    defer map.deinit();
=======
test "removeByPtr 0 sized key" {
    var map = AutoHashMap(u0, u64).init(testing.allocator);
    defer map.deinit();
>>>>>>> theirs

    try map.put(0, 0);

    try testing.expect(map.count() == 1);

    const key_ptr = map.getKeyPtr(0);
    try testing.expect(key_ptr != null);

    if (key_ptr) |ptr| {
        map.removeByPtr(ptr);
    }

    try testing.expect(map.count() == 0);
}

<<<<<<< ours
test "HashMap repeat fetchRemove" {
    const Map = AutoHashMapUnmanaged(u64, void);
    const cap = 64;
||||||| base
test "std.hash_map repeat fetchRemove" {
    var map = AutoHashMapUnmanaged(u64, void){};
    defer map.deinit(testing.allocator);
=======
test "repeat fetchRemove" {
    var map: AutoHashMapUnmanaged(u64, void) = .empty;
    defer map.deinit(testing.allocator);
>>>>>>> theirs

    const alloc = testing.allocator;
    const layout = Map.layoutForCapacity(cap);
    const buf = try alloc.alignedAlloc(u8, Map.base_align, layout.total_size);
    defer alloc.free(buf);
    var map = Map.init(.init(buf), layout);

    map.putAssumeCapacity(0, {});
    map.putAssumeCapacity(1, {});
    map.putAssumeCapacity(2, {});
    map.putAssumeCapacity(3, {});

    // fetchRemove() should make slots available.
    var i: usize = 0;
    while (i < 10) : (i += 1) {
        try testing.expect(map.fetchRemove(3) != null);
        map.putAssumeCapacity(3, {});
    }

    try testing.expect(map.get(0) != null);
    try testing.expect(map.get(1) != null);
    try testing.expect(map.get(2) != null);
    try testing.expect(map.get(3) != null);
}

test "OffsetHashMap basic usage" {
    const OffsetMap = AutoOffsetHashMap(u32, u32);
    const cap = 16;

    const alloc = testing.allocator;
    const layout = OffsetMap.layout(cap);
    const buf = try alloc.alignedAlloc(u8, OffsetMap.base_align, layout.total_size);
    defer alloc.free(buf);
    var offset_map = OffsetMap.init(.init(buf), layout);
    var map = offset_map.map(buf.ptr);

    const count = 5;
    var i: u32 = 0;
    var total: u32 = 0;
    while (i < count) : (i += 1) {
        try map.put(i, i);
        total += i;
    }

    var sum: u32 = 0;
    var it = map.iterator();
    while (it.next()) |kv| {
        sum += kv.key_ptr.*;
    }
    try expectEqual(total, sum);

    i = 0;
    sum = 0;
    while (i < count) : (i += 1) {
        try expectEqual(i, map.get(i).?);
        sum += map.get(i).?;
    }
    try expectEqual(total, sum);
}

test "OffsetHashMap remake map" {
    const OffsetMap = AutoOffsetHashMap(u32, u32);
    const cap = 16;

    const alloc = testing.allocator;
    const layout = OffsetMap.layout(cap);
    const buf = try alloc.alignedAlloc(u8, OffsetMap.base_align, layout.total_size);
    defer alloc.free(buf);
    var offset_map = OffsetMap.init(.init(buf), layout);

    {
        var map = offset_map.map(buf.ptr);
        try map.put(5, 5);
    }

    {
        var map = offset_map.map(buf.ptr);
        try expectEqual(5, map.get(5).?);
    }
}
// copyv: end
