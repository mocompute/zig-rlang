/// Represents a four-part version number: major, minor, patch, and
/// rev.
pub const Version = extern struct {
    major: u32 = 0,
    minor: u32 = 0,
    patch: u32 = 0,
    rev: u32 = 0,

    /// Parse a string into a Version.
    pub fn parse(string: []const u8) error{InvalidFormat}!Version {
        var major: u32 = 0;
        var minor: u32 = 0;
        var patch: u32 = 0;
        var rev: u32 = 0;

        const in = std.mem.trim(u8, string, &std.ascii.whitespace);

        // Format: r12345 (svn version)
        if (std.mem.startsWith(u8, in, "r")) {
            major = std.fmt.parseInt(u32, in[1..], 10) catch {
                return error.InvalidFormat;
            };
            return .{ .major = major };
        }

        // Format: segments may be separated by . or -
        var it = std.mem.splitAny(u8, in, ".-");
        if (it.next()) |maj| {
            major = std.fmt.parseInt(u32, maj, 10) catch {
                return error.InvalidFormat;
            };
        }

        if (it.next()) |min| {
            minor = std.fmt.parseInt(u32, min, 10) catch {
                return error.InvalidFormat;
            };
        }

        if (it.next()) |p| {
            patch = std.fmt.parseInt(u32, p, 10) catch {
                return error.InvalidFormat;
            };
        }

        if (it.next()) |p| {
            rev = std.fmt.parseInt(u32, p, 10) catch {
                return error.InvalidFormat;
            };
        }

        return .{
            .major = major,
            .minor = minor,
            .patch = patch,
            .rev = rev,
        };
    }

    /// Compare this version to another and return the mathematical order.
    pub fn order(self: Version, other: Version) std.math.Order {
        if (self.major > other.major) return .gt;
        if (self.major < other.major) return .lt;
        if (self.minor > other.minor) return .gt;
        if (self.minor < other.minor) return .lt;
        if (self.patch > other.patch) return .gt;
        if (self.patch < other.patch) return .lt;
        if (self.rev > other.rev) return .gt;
        if (self.rev < other.rev) return .lt;
        return .eq;
    }

    pub fn format(
        self: Version,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        if (self.rev > 0) {
            try writer.print("({}.{}.{}.{})", .{ self.major, self.minor, self.patch, self.rev });
        } else {
            try writer.print("({}.{}.{})", .{ self.major, self.minor, self.patch });
        }
    }
};

/// Enum to represent numerical ordering.
pub const Operator = enum(u8) {
    lt,
    lte,
    eq,
    gte,
    gt,

    /// Parse a string operator into its corresponding enum, or return
    /// an error. Input is a string that starts with an operator
    /// but may contain further data, which is ignored.
    pub fn parseLeft(operator: []const u8) error{InvalidFormat}!Operator {
        const startsWith = std.mem.startsWith;
        return if (startsWith(u8, operator, "<="))
            .lte
        else if (startsWith(u8, operator, "<"))
            .lt
        else if (startsWith(u8, operator, ">="))
            .gte
        else if (startsWith(u8, operator, ">"))
            .gt
        else if (startsWith(u8, operator, "="))
            .eq
        else
            error.InvalidFormat;
    }

    pub fn format(
        self: Operator,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        switch (self) {
            .lt => try writer.print("<", .{}),
            .lte => try writer.print("<=", .{}),
            .eq => try writer.print("==", .{}),
            .gte => try writer.print(">=", .{}),
            .gt => try writer.print(">", .{}),
        }
    }
};

/// Represents an ordered constraint on a version number.
pub const VersionConstraint = extern struct {
    operator: Operator = .gte,
    version: Version = .{},

    /// Initialise the struct.
    pub fn init(operator: Operator, version: Version) VersionConstraint {
        return .{ .operator = operator, .version = version };
    }

    /// Attempt to parse a string into a version and initialise the
    /// VersionConstraint struct, or return an error.
    pub fn parseOperatorVersion(operator: Operator, version: []const u8) !VersionConstraint {
        return .{ .operator = operator, .version = try Version.parse(version) };
    }

    /// Return true if other Version satisfies my version constraint.
    pub fn satisfied(self: VersionConstraint, other: Version) bool {
        const order = other.order(self.version);
        switch (self.operator) {
            .lt => return order == .lt,
            .lte => return order == .lt or order == .eq,
            .eq => return order == .eq,
            .gte => return order == .gt or order == .eq,
            .gt => return order == .gt,
        }
    }

    pub fn format(
        self: VersionConstraint,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("({} {?})", .{ self.operator, self.version });
    }
};

/// Represents a name and version constraint.
pub const PackageSpec = struct {
    name: []const u8,
    version_constraint: VersionConstraint = .{},

    /// Attempt to parse string into a name and optional version
    /// constraint. The format is `name (>= 3.2)` where the
    /// parenthetical expression is optional. The operators `=` and
    /// `==` are considered equal.
    pub fn parse(string: []const u8) error{InvalidFormat}!PackageSpec {
        const trim = std.mem.trim;

        const in = trim(u8, string, &std.ascii.whitespace);

        var name: []const u8 = "";
        var it = std.mem.splitAny(u8, in, "(" ++ &std.ascii.whitespace);
        if (it.next()) |s| {
            name = s;
        } else return error.InvalidFormat;

        if (name.len == 0 or !std.ascii.isAlphabetic(name[0])) return error.InvalidFormat;

        const rest = trim(u8, it.rest(), &std.ascii.whitespace);
        const inner = trim(
            u8,
            trim(u8, rest, "()"),
            &std.ascii.whitespace,
        );
        const constraint = Operator.parseLeft(inner) catch {
            // no constraint found
            return .{ .name = name };
        };

        // now trim off operators and whitespace, what's left is
        // the version string
        const ver = trim(u8, inner, "<>=" ++ std.ascii.whitespace);

        return .{
            .name = name,
            .version_constraint = try VersionConstraint.parseOperatorVersion(constraint, ver),
        };
    }

    /// Parse a comma-separated list of package specs. Caller owns returned slice.
    pub fn parseList(alloc: std.mem.Allocator, in: []const u8) error{
        InvalidFormat,
        OutOfMemory,
    }![]PackageSpec {
        return PackageSpec.parseListWithCapacity(alloc, in, 4);
    }

    /// Parse a comma-separated list of package specs. Allocate
    /// initial_capacity array. Caller owns returned slice.
    pub fn parseListWithCapacity(
        alloc: std.mem.Allocator,
        in: []const u8,
        initial_capacity: usize,
    ) error{
        InvalidFormat,
        OutOfMemory,
    }![]PackageSpec {
        var out = try std.ArrayList(PackageSpec).initCapacity(alloc, initial_capacity);
        defer out.deinit();

        var it = std.mem.splitScalar(u8, in, ',');
        while (it.next()) |x| {
            try out.append(try PackageSpec.parse(x));
        }

        return out.toOwnedSlice();
    }

    pub fn format(
        self: PackageSpec,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("({s} {s})", .{ self.name, self.version_constraint });
    }
};

/// Given a slice of constraints, attempt to merge them according to
/// our internal merge table. If a constraint violation is found,
/// returns error.NoIntersection. Caller must free returned slice.
/// Note: does not support two sided inequalities, this is for future
/// work (TODO).
pub fn mergePackageSpecs(
    alloc: std.mem.Allocator,
    in: []const PackageSpec,
) error{ OutOfMemory, NoIntersection }![]PackageSpec {
    var seen = try std.ArrayList(PackageSpec).initCapacity(alloc, in.len);

    outer: for (in) |navc| {
        for (seen.items) |*existing| {
            if (std.mem.eql(u8, navc.name, existing.name)) {
                if (mergeVersionConstraints(navc.version_constraint, existing.version_constraint)) |merged| {
                    existing.*.version_constraint = merged;
                } else {
                    return error.NoIntersection;
                }
                continue :outer;
            }
        }

        seen.appendAssumeCapacity(navc);
    }

    seen.shrinkAndFree(seen.items.len);
    return seen.toOwnedSlice();
}

// merge table

// zig fmt: off
const MergeOp = enum {
    o,                          // null
    two,                        // null, TODO: implement two-sided constraints
    lhs,                        // take left hand side
    rhs,                        // take right hand side
    eq_lhs,                     // new constraint .eq version of lhs
};

const MergeTableOrder = enum(usize) { lt, lte, eq, gte, gt };

// order compares lhs ? rhs.
const MergeOpOrder = enum(usize) {
    lt,                         // rhs < lhs
    eq,                         // rhs = lhs
    gt,                         // rhs > lhs
};

const MergeTable: [5][5][3]MergeOp = .{
    // lhs <
    .{
        .{.lhs, .lhs, .rhs },   // rhs <
        .{ .lhs, .lhs, .rhs },  // rhs <=
        .{ .o, .o, .rhs },      // rhs =
        .{ .o, .o, .two },      // rhs >=
        .{ .o, .o, .two },      // rhs >
    },

    // lhs <=
    .{
        .{ .lhs, .rhs, .rhs },  // rhs <
        .{ .lhs, .lhs, .rhs },  // rhs <=
        .{ .o, .rhs, .rhs },    // rhs =
        .{ .o, .eq_lhs, .two }, // rhs >=
        .{ .o, .o, .two },      // rhs >
    },

    // lhs =
    .{
        .{ .lhs, .o, .o },      // rhs <
        .{ .lhs, .lhs, .o },    // rhs <=
        .{ .o, .lhs, .o },      // rhs =
        .{ .o, .lhs, .lhs },    // rhs >=
        .{ .o, .o, .lhs },      // rhs >
    },

    // lhs >=
    .{
        .{ .two, .o, .o },      // rhs <
        .{ .two, .eq_lhs, .o }, // rhs <=
        .{ .rhs, .rhs, .o },    // rhs =
        .{ .rhs, .lhs, .lhs },  // rhs >=
        .{ .rhs, .rhs, .lhs },  // rhs >
    },

    // lhs >
    .{
        .{ .two, .o, .o },      // rhs <
        .{ .two, .o, .o },      // rhs <=
        .{ .rhs, .o, .o },      // rhs =
        .{ .rhs, .lhs, .lhs },  // rhs >=
        .{ .rhs, .lhs, .lhs },  // rhs >
    },
};
// zig fmt: on

fn operatorToTableIndex(op: Operator) usize {
    return switch (op) {
        .lt => @intFromEnum(MergeTableOrder.lt),
        .lte => @intFromEnum(MergeTableOrder.lte),
        .eq => @intFromEnum(MergeTableOrder.eq),
        .gte => @intFromEnum(MergeTableOrder.gte),
        .gt => @intFromEnum(MergeTableOrder.gt),
    };
}

/// Merge two version constraints if possible. Returns null otherwise.
fn mergeVersionConstraints(a: VersionConstraint, b: VersionConstraint) ?VersionConstraint {
    const row = operatorToTableIndex(a.operator);
    const col = operatorToTableIndex(b.operator);
    const order = switch (a.version.order(b.version)) {
        .lt => @intFromEnum(MergeOpOrder.lt),
        .eq => @intFromEnum(MergeOpOrder.eq),
        .gt => @intFromEnum(MergeOpOrder.gt),
    };

    return switch (MergeTable[row][col][order]) {
        .o => null,
        .two => null, // TODO: implement two-sided constraints
        .lhs => a,
        .rhs => b,
        .eq_lhs => VersionConstraint{ .operator = .eq, .version = a.version },
    };
}

const PackageListParser = struct {};

test "sanity" {
    try testing.expectEqual(1, 1);
}

test mergeVersionConstraints {
    const expectEqual = testing.expectEqual;

    const one = Version{ .major = 1 };
    const five = Version{ .major = 5 };
    const six = Version{ .major = 6 };

    const a = VersionConstraint{ .operator = .lt, .version = five };
    var op = Operator.lt;
    var b = VersionConstraint{ .operator = op, .version = one };

    op = Operator.lt;
    b = VersionConstraint{ .operator = op, .version = one };
    try expectEqual(b, mergeVersionConstraints(a, b));
    b = VersionConstraint{ .operator = op, .version = five };
    try expectEqual(a, mergeVersionConstraints(a, b));
    b = VersionConstraint{ .operator = op, .version = six };
    try expectEqual(a, mergeVersionConstraints(a, b));

    // no more tests as we're just testing that MergeTable is as we
    // expect it to be.
}

test mergePackageSpecs {
    const expectEqual = testing.expectEqual;
    const alloc = std.testing.allocator;

    const in = [_]PackageSpec{
        .{
            .name = "foo",
            .version_constraint = .{},
        },
        .{
            .name = "bar",
            .version_constraint = .{ .version = .{ .major = 5 } },
        },
        .{
            .name = "foo",
            .version_constraint = .{ .operator = .eq, .version = .{ .major = 5 } },
        },
    };

    const out = try mergePackageSpecs(alloc, &in);
    defer alloc.free(out);

    try expectEqual(2, out.len);
    for (out) |x| {
        if (std.mem.eql(u8, "foo", x.name)) {
            try expectEqual(VersionConstraint{ .operator = .eq, .version = .{ .major = 5 } }, x.version_constraint);
        }
    }
}

/// Provide equality and hash for an AutoHashMap of PackageSpec.
pub const PackageSpecContext = struct {
    pub fn eql(_: Self, a: PackageSpec, b: PackageSpec, _: usize) bool {
        if (!std.meta.eql(a.version_constraint, b.version_constraint)) return false;
        if (!std.mem.eql(u8, a.name, b.name)) return false;
        return true;
    }

    pub const hash = std.array_hash_map.getAutoHashStratFn(
        PackageSpec,
        Self,
        // we wish to deeply compare the name string
        .Deep,
    );
    const Self = @This();
};

test PackageSpecContext {
    const ctx = PackageSpecContext{};

    const a = PackageSpec{ .name = "foo" };
    const b = PackageSpec{ .name = "foo" };
    const c = PackageSpec{ .name = "bar" };

    try testing.expect(ctx.eql(a, a, 0));
    try testing.expect(ctx.eql(a, b, 0));
    try testing.expect(ctx.eql(b, a, 0));
    try testing.expectEqual(ctx.hash(a), ctx.hash(a));
    try testing.expectEqual(ctx.hash(a), ctx.hash(b));

    try testing.expect(!ctx.eql(a, c, 0));
    try testing.expect(!ctx.eql(c, a, 0));
    try testing.expect(ctx.hash(a) != ctx.hash(c));
}

pub const PackageSpecSortContext = struct {
    keys: []const PackageSpec,

    pub fn lessThan(ctx: @This(), a: usize, b: usize) bool {
        const a_navc = ctx.keys[a];
        const b_navc = ctx.keys[b];
        const a_name = a_navc.name;
        const b_name = b_navc.name;
        const len = @min(a_name.len, b_name.len);
        for (a_name[0..len], b_name[0..len]) |x, y| {
            if (x < y) return true;
            if (x > y) return false;
        }
        if (a_name.len < b_name.len) return true;

        const a_ver = a_navc.version_constraint;
        const b_ver = b_navc.version_constraint;
        const order = a_ver.version.order(b_ver.version);
        switch (order) {
            .lt => return true,
            .gt => return false,
            .eq => {
                return @intFromEnum(a_ver.operator) < @intFromEnum(b_ver.operator);
            },
        }
    }
};

test PackageSpecSortContext {
    const keys: []const PackageSpec = &.{
        .{ .name = "foo" },
        .{ .name = "bar" },
    };
    const ctx = PackageSpecSortContext{ .keys = keys };

    try testing.expect(ctx.lessThan(1, 0));
}

test "PackageSpec" {
    const expectEqual = testing.expectEqual;
    const expectEqualStrings = testing.expectEqualStrings;
    const expectError = testing.expectError;

    const v1 = try PackageSpec.parse("package");
    try expectEqualStrings("package", v1.name);
    try expectEqual(.gte, v1.version_constraint.operator);
    try expectEqual(0, v1.version_constraint.version.major);
    try expectEqual(0, v1.version_constraint.version.minor);
    try expectEqual(0, v1.version_constraint.version.patch);

    const v2 = try PackageSpec.parse("  pak  ( >= 2.0 ) ");
    try expectEqualStrings("pak", v2.name);
    try expectEqual(.gte, v2.version_constraint.operator);
    try expectEqual(2, v2.version_constraint.version.major);

    const v3 = try PackageSpec.parse("x(= 1)");
    try expectEqualStrings("x", v3.name);
    try expectEqual(.eq, v3.version_constraint.operator);
    try expectEqual(1, v3.version_constraint.version.major);

    const v4 = try PackageSpec.parse("x (=1)");
    try expectEqualStrings("x", v4.name);
    try expectEqual(.eq, v4.version_constraint.operator);
    try expectEqual(1, v4.version_constraint.version.major);

    try expectError(error.InvalidFormat, PackageSpec.parse("(= 1)"));
}

test "PackageSpec.parseList" {
    const allocator = std.testing.allocator;

    const v1 = try PackageSpec.parseList(allocator, "a, b (> 1), c (< 5.3)");
    defer allocator.free(v1);

    try testing.expectEqual(3, v1.len);
    try testing.expectEqualStrings("a", v1[0].name);
    try testing.expectEqual(.gte, v1[0].version_constraint.operator);
    try testing.expectEqual(0, v1[0].version_constraint.version.major);
    try testing.expectEqual(0, v1[0].version_constraint.version.minor);
    try testing.expectEqual(0, v1[0].version_constraint.version.patch);

    try testing.expectEqualStrings("b", v1[1].name);
    try testing.expectEqual(.gt, v1[1].version_constraint.operator);
    try testing.expectEqual(1, v1[1].version_constraint.version.major);
    try testing.expectEqual(0, v1[1].version_constraint.version.minor);
    try testing.expectEqual(0, v1[1].version_constraint.version.patch);

    try testing.expectEqualStrings("c", v1[2].name);
    try testing.expectEqual(.lt, v1[2].version_constraint.operator);
    try testing.expectEqual(5, v1[2].version_constraint.version.major);
    try testing.expectEqual(3, v1[2].version_constraint.version.minor);
    try testing.expectEqual(0, v1[2].version_constraint.version.patch);
}

test "VersionConstraint" {
    const expect = testing.expect;

    const v1 = try VersionConstraint.parseOperatorVersion(.gte, "0");
    try expect(v1.satisfied(try Version.parse("1.0")));
    try expect(v1.satisfied(try Version.parse("0.0")));

    const v2 = try VersionConstraint.parseOperatorVersion(.gte, "3.2.4");
    try expect(v2.satisfied(try Version.parse("3.2.4")));
    try expect(v2.satisfied(try Version.parse("3.2.5")));
    try expect(v2.satisfied(try Version.parse("3.3.4")));
    try expect(v2.satisfied(try Version.parse("4.0.0")));
    try expect(!v2.satisfied(try Version.parse("3")));
    try expect(!v2.satisfied(try Version.parse("3.2.3")));
    try expect(!v2.satisfied(try Version.parse("3.1.4")));
    try expect(!v2.satisfied(try Version.parse("2.2.4")));

    const v3 = try VersionConstraint.parseOperatorVersion(.lte, "1.2.3");
    try expect(v3.satisfied(try Version.parse("1.2.3")));
    try expect(v3.satisfied(try Version.parse("1.2.2")));
    try expect(!v3.satisfied(try Version.parse("1.2.4")));
}

test "Version.init" {
    const expectEqual = testing.expectEqual;
    const expectError = testing.expectError;

    const v1 = try Version.parse("1.2.3");
    try expectEqual(1, v1.major);
    try expectEqual(2, v1.minor);
    try expectEqual(3, v1.patch);

    const v2 = try Version.parse("r1234");
    try expectEqual(1234, v2.major);
    try expectEqual(0, v2.minor);
    try expectEqual(0, v2.patch);

    const v3 = try Version.parse("1");
    try expectEqual(1, v3.major);
    try expectEqual(0, v3.minor);
    try expectEqual(0, v3.patch);

    const v4 = try Version.parse("1.2");
    try expectEqual(1, v4.major);
    try expectEqual(2, v4.minor);
    try expectEqual(0, v4.patch);

    const v5 = try Version.parse("0.2");
    try expectEqual(0, v5.major);
    try expectEqual(2, v5.minor);
    try expectEqual(0, v5.patch);

    try expectError(error.InvalidFormat, Version.parse("v123"));
    try expectError(error.InvalidFormat, Version.parse("r123.32"));
    try expectError(error.InvalidFormat, Version.parse(".32"));

    try expectError(error.InvalidFormat, Version.parse("-3.0.4"));
}

test "Version.order" {
    const expectEqual = testing.expectEqual;

    try expectEqual(.gt, (try Version.parse("1")).order(try Version.parse("0")));
    try expectEqual(.lt, (try Version.parse("0")).order(try Version.parse("1")));
    try expectEqual(.eq, (try Version.parse("1")).order(try Version.parse("1")));

    try expectEqual(.gt, (try Version.parse("1.1")).order(try Version.parse("1")));
    try expectEqual(.gt, (try Version.parse("1.1")).order(try Version.parse("1.0")));
    try expectEqual(.gt, (try Version.parse("1.1")).order(try Version.parse("1.0.1")));

    try expectEqual(.lt, (try Version.parse("1.0.0")).order(try Version.parse("1.0.1")));
    try expectEqual(.eq, (try Version.parse("1.0.0")).order(try Version.parse("1.0.0")));

    try expectEqual(.gt, (try Version.parse("1.0.1")).order(try Version.parse("1.0.0")));
    try expectEqual(.lt, (try Version.parse("1.0.0")).order(try Version.parse("1.0.1")));
    try expectEqual(.eq, (try Version.parse("1.0.0")).order(try Version.parse("1.0.0")));

    try expectEqual(.gt, (try Version.parse("1.1")).order(try Version.parse("1.0.5")));
    try expectEqual(.lt, (try Version.parse("0")).order(try Version.parse("1")));
}

test "version with 4 fields" {
    const expectEqual = testing.expectEqual;
    const v1 = try Version.parse("1.2.3-456");
    try expectEqual(1, v1.major);
    try expectEqual(2, v1.minor);
    try expectEqual(3, v1.patch);
    try expectEqual(456, v1.rev);
}

const std = @import("std");
const testing = std.testing;
