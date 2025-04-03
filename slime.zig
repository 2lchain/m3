const std = @import("std");
const elf = std.elf;
const testing = std.testing;

const elf_path = ".\\zig-out\\bin\\code";

//[_]u8{0xff} ** (1024 * 1024 * 10);

fn sint32(n: u8, bits: u32) i32 {
    std.debug.assert(n > 0);

    const p: u32 = std.math.pow(u32, 2, n);
    const p2: u32 = std.math.pow(u32, 2, n - 1);

    var res: u32 = bits & p - 1;
    //std.debug.print("p: 0b{b}, bits: 0b{b}, res: {}\n", .{p,bits, res});
    //_= bits;
    if (p2 & res == p2) {
        res |= ~p2;
        //std.debug.print("signed!! {b} {}\n", .{res, @as(i32,@bitCast(res))});
    }
    return @as(i32, @bitCast(res));
}

fn uint32(n: u8, bits: u32) u32 {
    std.debug.assert(n > 0);
    const p: u32 = std.math.pow(u32, 2, n);
    //const p2:u32 = std.math.pow(u32, 2, n-1);
    return bits & p - 1;
}

pub const SRType = enum(u8) {
    ommited,
    lsl,
    lsr,
    asr,
    ror,
    rrx,
};

fn decodeImmShift(t: u2, imm: u5) struct { t: SRType, n: u8 } {
    return switch (t) {
        0b00 => .{ .t = .lsl, .n = @as(u5, @bitCast(imm)) },
        0b01 => .{ .t = .lsr, .n = if (imm == 0) 32 else @as(u5, @bitCast(imm)) },
        0b10 => .{ .t = .asr, .n = if (imm == 0) 32 else @as(u5, @bitCast(imm)) },
        0b11 => if (imm == 0) .{ .t = .rrx, .n = 1 } else .{ .t = .ror, .n = @as(u5, @bitCast(imm)) },
    };
}

fn decodeRegShift(t: u2) SRType {
    return switch (t) {
        0b00 => .lsl,
        0b01 => .lsr,
        0b10 => .asr,
        0b11 => .ror,
    };
}

//fn shift32(value: u32, t: SRType, amount: u8, carry: bool) u32 {
//
//}

const ShiftRes = struct { value: u32, carry: bool };

fn shiftc32(value: u32, t: SRType, amount: u6, carry: bool) ShiftRes {
    std.debug.assert(!(t == .rrx and amount != 1));
    if (amount == 0) return .{ .value = value, .carry = carry };
    return switch (t) {
        .lsl => lslc32(value, amount),
        .lsr => lsrc32(value, amount),
        .ror => rorc32(value, amount),
        .asr => asrc32(value, amount),
        .rrx => rrxc32(value, carry),
        else => unreachable,
    };
}

fn shift32(value: u32, t: SRType, amount: u6, carry: bool) u32 {
    // TODO allow overflow
    return shiftc32(value, t, amount, carry).value;
}

fn lslc32(value: u32, n: u6) ShiftRes {
    std.debug.assert(n > 0);
    const res = @as(u64, @intCast(value)) << (n - 1);
    const c = res & 0x80000000 > 0;
    return .{ .value = @truncate(res << 1), .carry = c };
}

fn lsl32(value: u32, n: u6) u32 {
    if (n == 0) return value;
    return lslc32(value, n).value;
}

test "lsl" {
    try testing.expectEqual(lslc32(1, 1), ShiftRes{ .carry = false, .value = 0b10 });
    try testing.expectEqual(lslc32(1, 32), ShiftRes{ .carry = true, .value = 0b0 });
    try testing.expectEqual(lslc32(1, 31), ShiftRes{ .carry = false, .value = 0x80000000 });
}

fn lsrc32(value: u32, n: u6) ShiftRes {
    std.debug.assert(n > 0);
    const res = @as(u64, @intCast(value)) >> (n - 1);
    const c = res & 1 > 0;
    return .{ .value = @truncate(res >> 1), .carry = c };
}

fn lsr32(value: u32, n: u6) u32 {
    if (n == 0) return value;
    return lsrc32(value, n).value;
}

test "lsr" {
    try testing.expectEqual(lsrc32(1, 1), ShiftRes{ .carry = true, .value = 0b0 });
    try testing.expectEqual(lsrc32(0b10, 1), ShiftRes{ .carry = false, .value = 0b1 });
    try testing.expectEqual(lsrc32(0x80000001, 32), ShiftRes{ .carry = true, .value = 0b0 });
}

fn asrc32(value: u32, n: u6) ShiftRes {
    std.debug.assert(n > 0);
    var res: i64 = @intCast(@as(i32, @bitCast(value)));
    res >>= (n - 1);
    const c = res & 1 > 0;
    return .{ .value = @bitCast(@as(i32, @truncate(res >> 1))), .carry = c };
}

fn asr32(value: u32, n: u6) u32 {
    if (n == 0) return value;
    return asrc32(value, n).value;
}

test "asr" {
    try testing.expectEqual(asrc32(0, 1), ShiftRes{ .carry = false, .value = 0 });
    try testing.expectEqual(asrc32(1, 1), ShiftRes{ .carry = true, .value = 0 });
    try testing.expectEqual(asrc32(0b10, 2), ShiftRes{ .carry = true, .value = 0 });
    try testing.expectEqual(asrc32(0x80000001, 3), ShiftRes{ .carry = false, .value = 0xf000_0000 });
    try testing.expectEqual(asrc32(0x80000001, 32), ShiftRes{ .carry = true, .value = 0xffff_ffff });
}

fn rorc32(value: u32, n: u6) ShiftRes {
    std.debug.assert(n != 0);
    const m = n % 32;
    const a = lsrc32(value, m).value | lslc32(value, 32 - m).value;
    return .{ .carry = a & 0x80000000 > 0, .value = a };
}

fn ror32(value: u32, n: u6) u32 {
    if (n == 0) return value;
    return rorc32(value, n).value;
}

test "rorc32" {
    try testing.expectEqual(rorc32(0b1, 1), ShiftRes{ .carry = true, .value = 0x80000000 });
    try testing.expectEqual(rorc32(0b101, 1), ShiftRes{ .carry = true, .value = 0x80000002 });
    try testing.expectEqual(rorc32(0b100, 1), ShiftRes{ .carry = false, .value = 0x00000002 });
}

fn rrxc32(value: u32, carry: bool) ShiftRes {
    const c = value & 1 > 0;
    var res = value >> 1;
    if (carry) res |= 0x80000000;
    return ShiftRes{ .carry = c, .value = res };
}

fn rrx32(value: u32, carry: bool) u32 {
    return rrxc32(value, carry).value;
}

test "rrx" {
    try testing.expectEqual(rrxc32(1, true), ShiftRes{ .carry = true, .value = 0x80000000 });
    try testing.expectEqual(rrxc32(1, false), ShiftRes{ .carry = true, .value = 0x0 });
}
pub fn mairn() !void {
    // const neg: i5 = -1;
    //const a: u32 = 0x80000000;
    // const n = addWithCarry32(127, 0, true);
    std.debug.print("res: {}\n", .{unsignedSat32(0)});
}

const SAT = struct { value: u32, sat: bool };

fn signedSat32(a: u32) bool {
    const i = @as(i32, @bitCast(a));
    return i >= std.math.maxInt(i32) or i <= std.math.minInt(i32);
}

fn unsignedSat32(a: u32) bool {
    return a >= std.math.maxInt(u32) or a <= 0;
}

fn sat32(a: u32, sign: bool) bool {
    if (sign) return signedSat32(a);
    return unsignedSat32(a);
}

const ADC = struct { carry_out: bool, overflow: bool, v: u32 };

fn addWithCarry32(a: u32, b: u32, carry: bool) ADC {
    var carry_out = false;
    var overflow = false;
    var ss = @addWithOverflow(@as(i32, @bitCast(a)), @as(i32, @bitCast(b)));
    var us = @addWithOverflow(a, b);

    carry_out = us[1] == 1;
    overflow = ss[1] == 1;

    ss = @addWithOverflow(@as(i32, @bitCast(ss[0])), @as(i32, @intFromBool(carry)));
    us = @addWithOverflow(us[0], @intFromBool(carry));

    if (carry_out == false) carry_out = us[1] == 1;
    if (overflow == false) overflow = ss[1] == 1;

    std.debug.assert(@as(u32, @bitCast(ss[0])) == us[0]);

    return .{ //
        .carry_out = carry_out,
        .overflow = overflow,
        .v = us[0],
    };
}

test "adc" {
    try testing.expectEqual(addWithCarry32(0, 0, true), ADC{ //
        .carry_out = false,
        .overflow = false,
        .v = 1,
    });
    try testing.expectEqual(addWithCarry32(std.math.maxInt(i32), 0, true), ADC{ //
        .carry_out = false,
        .overflow = true,
        .v = 0x8000_0000,
    });
    try testing.expectEqual(addWithCarry32(std.math.maxInt(i32) - 1, 1, true), ADC{ //
        .carry_out = false,
        .overflow = true,
        .v = 0x8000_0000,
    });
    try testing.expectEqual(addWithCarry32(std.math.maxInt(u32), 1, true), ADC{ //
        .carry_out = true,
        .overflow = false,
        .v = 1,
    });
    try testing.expectEqual(addWithCarry32(0x8000_0000, 0x8000_0000, false), ADC{ //
        .carry_out = true,
        .overflow = true,
        .v = 0,
    });
}

test "main" {
    testing.refAllDecls(Cpu);
}

fn bitCount(T: type, v: T) u8 {
    var a = v;
    var r: u8 = 0;
    for (0..@bitSizeOf(T)) |_| {
        if (a & 1 > 0) r += 1;
        a >>= 1;
    }
    return r;
}

test "bitcount" {
    try testing.expectEqual(3, bitCount(u8, 0b111));
}

fn lowestSetBit(T: type, v: T) u8 {
    var a = v;
    for (0..@bitSizeOf(T)) |i| {
        if (a & 1 > 0) return @truncate(i);
        a >>= 1;
    }
    return @bitSizeOf(T) - 1;
}

test "lwstbitset" {
    try testing.expectEqual(0, lowestSetBit(u8, 1));
    try testing.expectEqual(7, lowestSetBit(u8, 128));
    try testing.expectEqual(4, lowestSetBit(u8, 0xf0));
}

const ExpandedImm = struct { val: u32, carry: bool };

fn thumbExpandImmC(bits: u12, carry: bool) ExpandedImm {
    const a = @as(packed struct(u12) { //
        _7_0: u8,
        _9_8: u2,
        _11_10: u2,
    }, @bitCast(bits));

    if (a._11_10 == 0) {
        return switch (a._9_8) {
            0b00 => .{ .carry = carry, .val = a._7_0 },
            0b01 => .{ //
                .carry = carry,
                .val = (@as(u32, a._7_0) << 16) | @as(u32, a._7_0),
            },
            0b10 => .{ //
                .carry = carry,
                .val = (@as(u32, a._7_0) << 24) | (@as(u32, a._7_0) << 8),
            },
            0b11 => .{ //
                .carry = carry,
                .val = (@as(u32, a._7_0) << 24) | (@as(u32, a._7_0) << 16) | (@as(u32, a._7_0) << 8) | @as(u32, a._7_0),
            },
        };
    } else {
        const res = rorc32(a._7_0 | 128, @intCast(bits >> 7));
        return .{ .carry = res.carry, .val = res.value };
    }
}

test "thumbExpandImm" {
    const T = packed struct(u12) { //
        _7_0: u8,
        _9_8: u2,
        _11_10: u2,
    };

    var a = T{ ._9_8 = 0, ._7_0 = 0xff, ._11_10 = 0 };
    try testing.expect(thumbExpandImmC(@bitCast(a), false).val == 0xff);
    a._9_8 = 1;
    try testing.expect(thumbExpandImmC(@bitCast(a), false).val == 0xff00ff);
    a._9_8 = 2;
    try testing.expect(thumbExpandImmC(@bitCast(a), false).val == 0xff00ff00);
    a._9_8 = 3;
    try testing.expect(thumbExpandImmC(@bitCast(a), false).val == 0xffffffff);
    a._9_8 = 0;
    a._11_10 = 1;
    a._7_0 = 0;
    try testing.expect(thumbExpandImmC(@bitCast(a), false).val == 0x8000_0000);
    try testing.expect(thumbExpandImmC(@bitCast(a), false).carry);
}

const Cpu = struct {
    const Mode = enum { thread, handler };

    const Exception = enum(u8) { //
        reset,
        nmi,
        hardfault,
        memmanage,
        busfault,
        usagefault,
        svccall = 11,
        debugmonitor,
        pendsv = 14,
        systick,
        _,
    };

    const ITSTATE = packed struct(u8) {
        rest: u4,
        condition: u4,

        pub fn in(self: *const ITSTATE) bool {
            return @as(u8, @bitCast(self.*)) & 0b1111 != 0;
        }

        pub fn last(self: *const ITSTATE) bool {
            return @as(u8, @bitCast(self.*)) & 0b1111 == 0b1000;
        }

        pub inline fn clear(self: *ITSTATE) void {
            self.* = @bitCast(@as(u8, 0));
        }

        pub fn advance(self: *ITSTATE) void {
            if (self.rest & 0b111 == 0) {
                self.clear();
            } else {
                self.rest <<= 1;
            }
        }

        pub fn getIt(self: *const ITSTATE) u8 {
            return @as(u8, @bitCast(self.*));
        }

        pub fn setIt(self: *ITSTATE, bits: u8) void {
            const p: *u8 = @ptrCast(self);
            p.* = p.* | bits;
        }

        fn init(back: u8) ITSTATE {
            return @bitCast(back);
        }

        fn cond(self: *const ITSTATE) u4 {
            return @truncate(self.getIt() >> 4);
        }

        test {
            var psr = Cpu.PSR{};
            var it = ITSTATE{ .rest = 0b1111, .condition = 0b1111 };
            psr.setIT(it.getIt());
            it = psr.getIT();
            try testing.expectEqual(true, it.in());
            //it.advance();
            psr.advanceIT();
            it = psr.getIT();
            try testing.expectEqual(0b11111110, it.getIt());
            psr.advanceIT();
            it = psr.getIT();
            try testing.expectEqual(0b11111100, it.getIt());
            psr.advanceIT();
            it = psr.getIT();
            try testing.expectEqual(0b11111000, it.getIt());
            try testing.expectEqual(true, it.last());
            psr.advanceIT();
            it = psr.getIT();
            try testing.expectEqual(0, it.getIt());
        }
    };

    test "cpu" {
        testing.refAllDecls(ITSTATE);
    }

    pub const PSR = packed struct(u32) {
        n: bool = false,
        z: bool = false,
        c: bool = false,
        v: bool = false,
        q: bool = false,
        ici_it: u2 = 0,
        t: bool = false,
        _res: u8 = 0,
        ici_it2: u4 = 0,
        ici_it3: u2 = 0,
        a: bool = false,
        exception: u9 = 0,

        fn getIT(self: *const PSR) ITSTATE {
            return ITSTATE.init(self.ici_it | (@as(u8, self.ici_it3) << 2) | @as(u8, self.ici_it2) << 4);
        }

        fn setIT(self: *PSR, back: u8) void {
            self.ici_it = @truncate(back);
            self.ici_it2 = @truncate(back >> 4);
            self.ici_it3 = @truncate(back >> 2);
        }

        fn advanceIT(self: *PSR) void {
            var it = self.getIT();
            it.advance();
            self.setIT(it.getIt());
        }

        fn setITALL(self: *PSR) void {
            self.setIT(0xff);
        }
    };

    const SP_MAIN = 13;
    const SP_PROC = 15;

    const SP_REG = 13;

    const CONTROL = packed struct(u32) { //
        zero: bool = false,
        one: bool = false,
        _r: u30 = 0,
    };

    const PRIMASK = packed struct(u32) { pm: bool = false, rest: u31 = 0 };
    const FAULTMASK = packed struct(u32) { fm: bool = false, rest: u31 = 0 };
    const BASEPRI = packed struct(u32) { basepri: u8 = 0, rest: u24 = 0 };

    memory: [1024 * 1024 * 10]u8 = undefined,
    mem_steam: std.io.FixedBufferStream([]u8) = undefined,

    regs: [16]u32 = undefined,
    psr: PSR = PSR{},
    primask: PRIMASK = .{},
    faultmask: FAULTMASK = .{},
    basepri: BASEPRI = .{},
    decoder: Decoder = undefined,
    mode: Mode = .thread,
    control: CONTROL = CONTROL{},

    fn currentModeIsPrivileged(self: *Cpu) bool {
        return switch (self.getMode()) {
            .handler => true,
            else => return self.control.zero,
        };
    }

    fn getMode(self: *Cpu) Mode {
        return self.mode;
    }

    fn init(self: *Cpu, path: []const u8) !void {
        const cwd = std.fs.cwd();
        const elf_file = try cwd.openFile(path, .{});
        var elf_header = try elf.Header.read(elf_file);
        std.debug.assert(elf_header.machine == elf.EM.ARM);
        var ph_iter = elf_header.program_header_iterator(elf_file);
        while (try ph_iter.next()) |ph| {
            if (ph.p_type != elf.PT_LOAD) continue;
            try elf_file.seekTo(ph.p_offset);
            const n = try elf_file.reader().readAll(self.memory[ph.p_vaddr..][0..ph.p_filesz]);
            std.debug.assert(n == ph.p_filesz);
        }

        self.mode = .thread;
        self.control = .{};

        self.basepri = .{};
        self.primask = .{};
        self.faultmask = .{};

        self.psr = .{ .t = true };

        self.mem_steam = std.io.fixedBufferStream(self.memory[0..]);

        self.decoder = try Decoder.init(elf_header.entry, elf_header.endian, self.memory[0..]);
    }

    fn currentCondition() u4 {
        return switch (cpu.decoder.current_instr) {
            .bT1 => return @truncate(((cpu.decoder.current >> 8) & 0b1111)),
            .bT3 => unreachable,
            else => cpu.psr.getIT().cond(),
        };
    }

    fn thumbExpandImm(self: *Cpu, bits: u12) u32 {
        return thumbExpandImmC(bits, self.psr.c).val;
    }

    fn conditionPassed(self: *Cpu) bool {
        const cond = currentCondition();
        const res = switch (cond >> 1) {
            0b000 => self.psr.z,
            0b001 => self.psr.c,
            0b010 => self.psr.n,
            0b011 => self.psr.v,
            0b100 => self.psr.c and self.psr.z,
            0b101 => self.psr.n == self.psr.v,
            0b110 => self.psr.n == self.psr.v and !self.psr.z,
            0b111 => true,
            else => unreachable,
        };

        if ((cond & 1) > 0 and cond != 0b1111) return !res;
        return res;
    }

    fn _lookUpSp(self: *const Cpu) usize {
        if (self.control.one) {
            if (self.mode == .thread) return 15;
            return SP_PROC;
        }
        return SP_MAIN;
    }

    fn getReg(self: *Cpu, n: usize) u32 {
        std.debug.assert(n <= 15);
        //if(n <= 15) return self.regs[n];
        if (n == 15) return self.getPC();
        if (n == 13) return self.regs[self._lookUpSp()];
        return self.regs[n];
    }

    fn setReg(self: *Cpu, n: usize, value: u32) void {
        std.debug.assert(n <= 14);
        if (n == 13) {
            self.regs[self._lookUpSp()] = value;
        } else {
            self.regs[n] = value;
        }
    }

    fn branchTo(self: *Cpu, addr: u32) void {
        self.setPC(@intCast(addr));
    }

    fn branchWritePC(self: *Cpu, addr: u32) void {
        self.branchTo(addr & 0xfffffffe);
    }

    fn bxWrtePC(self: *Cpu, addr: u32) void {
        if (self.getMode() == .handler and (addr & 0xf000_0000) == 0xf000_0000) {
            //TODO
            @panic("unhandled case!!");
        } else {
            self.psr.t = addr & 1 == 1;
            self.branchTo(addr & 0xffff_fffe);
        }
    }

    fn loadWritePC(self: *Cpu, addr: u32) void {
        self.bxWrtePC(addr);
    }

    fn aluWritePc(self: *Cpu, addr: u32) void {
        self.branchWritePC(addr);
    }

    fn getPC(self: *const Cpu) u32 {
        return @truncate(self.decoder.stream.pos + 4);
    }

    fn getRL(self: *const Cpu) u32 {
        return self.getReg(14);
    }

    fn setRL(self: *Cpu, v: u32) void {
        self.setReg(14, v);
    }

    //fn getPCOfft_(self: *const Cpu) u32 {
    //    return @truncate(self.decoder.stream.pos + 4);
    //}

    fn setPC(self: *Cpu, ip: u32) void {
        self.decoder.stream.pos = ip;
    }

    fn execPriortity(self: *Cpu) i8 {
        _ = self;
        return 0;
    }

    fn fetch(self: *Cpu) !Instr {
        return try self.decoder.decode();
    }

    fn readMemA(self: *Cpu, T: type, addr: usize) T {
        if (addr % @sizeOf(T) != 0) @panic("unaligned mem access!!");
        self.mem_steam.seekTo(addr) catch unreachable;
        //TODO check endian
        return self.mem_steam.reader().readInt(T, .big) catch unreachable;
    }

    fn writeMemA(self: *Cpu, T: type, addr: usize, val: T) void {
        if (addr % @sizeOf(T) != 0) @panic("unaligned mem access!!");
        self.mem_steam.seekTo(addr) catch unreachable;
        //TODO check endian
        self.mem_steam.writer().writeInt(T, val, .big) catch unreachable;
    }

    fn readMemU(self: *Cpu, T: type, addr: usize) T {
        self.mem_steam.seekTo(addr) catch unreachable;
        //TODO check endian
        return self.mem_steam.reader().readInt(T, .big) catch unreachable;
    }

    fn writeMemU(self: *Cpu, T: type, addr: usize, val: T) void {
        self.mem_steam.seekTo(addr) catch unreachable;
        //TODO check endian
        self.mem_steam.writer().writeInt(T, val, .big) catch unreachable;
    }

    fn ldmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, n: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            var bits = a.imm;
            var address = self.getReg(a.n);
            var wback = false;
            for (0..8) |i| {
                if (bits & 1 == 1) {
                    self.setReg(i, self.readMemA(u32, address));
                    address += 4;
                } else {
                    if (i == a.n) wback = true;
                }
                bits >>= 1;
            }
            if (wback) self.setReg(a.n, address);
        }
    }

    fn stmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, n: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            var bits = a.imm;
            var address = self.getReg(a.n);
            const lwbs = lowestSetBit(u8, a.imm);
            for (0..8) |i| {
                if (bits & 1 == 1) {
                    if (i == a.n and i != lwbs) {
                        // unknown
                    } else {
                        self.writeMemA(u32, address, self.getReg(i));
                    }
                    address += 4;
                }
                bits >>= 1;
            }
            self.setReg(a.n, address);
        }
    }

    fn addspimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, d: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = addWithCarry32(self.getReg(SP_REG), (@as(u32, a.imm) << 2), false);
            self.setReg(a.d, r.v);
        }
    }

    fn adrT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, d: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = std.mem.alignForward(u32, self.getPC(), 4) + (@as(u32, a.imm) << 2);
            self.setReg(a.d, r);
        }
    }

    fn ldrlitT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, t: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const addr = std.mem.alignForward(u32, self.getPC(), 4) + (@as(u32, a.imm) << 2);
            const data = self.readMemU(u32, addr);
            if (a.t == 15) {
                if (addr & 1 == 0) {
                    self.loadWritePC(data);
                }
            } else {
                self.setReg(a.t, data);
            }
        }
    }

    fn asrT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { d: u3, m: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = shiftc32(self.getReg(a.m), .asr, @intCast(a.imm), self.psr.c);
            self.setReg(a.d, r.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.value & 0x8000_0000 != 0;
                self.psr.z = r.value == 0;
                self.psr.c = r.carry;
            }
        }
    }

    fn lsrT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { d: u3, m: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = shiftc32(self.getReg(a.m), .lsr, @intCast(a.imm), self.psr.c);
            self.setReg(a.d, r.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.value & 0x8000_0000 != 0;
                self.psr.z = r.value == 0;
                self.psr.c = r.carry;
            }
        }
    }

    fn lslT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { d: u3, m: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            if (a.imm == 0) {
                return self.movregT2();
            }
            const r = shiftc32(self.getReg(a.m), .lsl, @intCast(a.imm), self.psr.c);
            self.setReg(a.d, r.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.value & 0x8000_0000 != 0;
                self.psr.z = r.value == 0;
                self.psr.c = r.carry;
            }
        }
    }

    fn addimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, n: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = addWithCarry32(self.getReg(a.n), a.imm, false);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    fn subimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, n: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = addWithCarry32(self.getReg(a.n), ~@as(u32, a.imm), true);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    fn cmpimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, n: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = addWithCarry32(self.getReg(a.n), ~@as(u32, a.imm), true);
            self.psr.n = r.v & 0x8000_0000 != 0;
            self.psr.z = r.v == 0;
            self.psr.c = r.carry_out;
            self.psr.v = r.overflow;
        }
    }

    fn movimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, d: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r: u32 = a.imm;
            self.setReg(a.d, r);
            if (!self.psr.getIT().in()) {
                self.psr.n = r & 0x8000_0000 != 0;
                self.psr.z = r == 0;
            }
        }
    }

    fn subimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { d: u3, n: u3, m: u3, r: u7 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = addWithCarry32(self.getReg(a.n), ~@as(u32, a.m), true);
            self.setReg(a.d, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    fn addimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { d: u3, n: u3, m: u3, r: u7 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = addWithCarry32(self.getReg(a.n), a.m, false);

            self.setReg(a.d, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    fn subregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { d: u3, n: u3, m: u3, r: u7 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = addWithCarry32(self.getReg(a.n), ~self.getReg(a.m), true);
            self.setReg(a.d, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    fn addregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { d: u3, n: u3, m: u3, r: u7 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const r = addWithCarry32(self.getReg(a.n), self.getReg(a.m), false);
            if (a.d == 15) {
                self.aluWritePc(r.v);
            } else {
                self.setReg(a.d, r.v);
                if (!self.psr.getIT().in()) {
                    self.psr.n = r.v & 0x8000_0000 != 0;
                    self.psr.z = r.v == 0;
                    self.psr.c = r.carry_out;
                    self.psr.v = r.overflow;
                }
            }
        }
    }

    fn mvnregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = ~self.getReg(a.m);
            self.setReg(a.dn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    fn bicregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = ~self.getReg(a.m) & self.getReg(a.dn);
            self.setReg(a.dn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    fn mulT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = @mulWithOverflow(self.getReg(a.m), self.getReg(a.dn))[0];
            self.setReg(a.dn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    fn orrregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = self.getReg(a.m) | self.getReg(a.dn);
            self.setReg(a.dn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    fn cmnregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { n: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const n = a.n;
            const r = addWithCarry32(self.getReg(n), self.getReg(a.m), false);

            self.psr.n = r.v & 0x8000_0000 != 0;
            self.psr.z = r.v == 0;
            self.psr.c = r.carry_out;
            self.psr.v = r.overflow;
        }
    }

    fn rsbimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { d: u3, n: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = addWithCarry32(~self.getReg(a.n), 0, true);
            self.setReg(a.d, res.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    fn tstregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = self.getReg(a.m) & self.getReg(a.dn);
            self.setReg(a.dn, res);

            self.psr.n = res & 0x8000_0000 != 0;
            self.psr.z = res == 0;
        }
    }

    fn rorregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const shift_n: u6 = @intCast(self.getReg(a.m) & 0xff);
            const res = shiftc32(self.getReg(a.dn), .ror, shift_n, self.psr.c);
            self.setReg(a.dn, res.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    fn sbcregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = addWithCarry32(self.getReg(a.dn), ~self.getReg(a.m), self.psr.c);
            self.setReg(a.dn, res.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    fn adcregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = addWithCarry32(self.getReg(a.dn), self.getReg(a.m), self.psr.c);
            self.setReg(a.dn, res.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    fn asrregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const shift_n: u6 = @intCast(self.getReg(a.m) & 0xff);
            const res = shiftc32(self.getReg(a.dn), .asr, shift_n, self.psr.c);
            self.setReg(a.dn, res.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    fn lsrregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const shift_n: u6 = @intCast(self.getReg(a.m) & 0xff);
            const res = shiftc32(self.getReg(a.dn), .lsr, shift_n, self.psr.c);
            self.setReg(a.dn, res.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    fn lslregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const shift_n: u6 = @intCast(self.getReg(a.m) & 0xff);
            const res = shiftc32(self.getReg(a.dn), .lsl, shift_n, self.psr.c);
            self.setReg(a.dn, res.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    fn eorregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = self.getReg(a.m) ^ self.getReg(a.dn);
            self.setReg(a.dn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }
    fn andregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dn: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const res = self.getReg(a.m) & self.getReg(a.dn);
            self.setReg(a.dn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    fn blxregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { d: u3, m: u4, D: u1 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const target = self.getReg(a.m);
            self.setRL((self.getPC() - 2) | 1);
            self.bxWrtePC(target);
        }
    }

    fn bxT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { d: u3, m: u4, D: u1 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            self.bxWrtePC(self.getReg(a.m));
        }
    }

    fn movregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { d: u3, m: u3, D: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const d = a.d;
            const r = self.getReg(a.m);
            if (d == 15) {
                self.aluWritePc(r);
            } else {
                self.setReg(d, r);
                self.psr.n = r & 0x8000_0000 != 0;
                self.psr.z = r == 0;
            }
        }
    }

    fn movregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { d: u3, m: u4, D: u1 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const d = (@as(u4, a.D) << 3) | a.d;
            const result = self.getReg(a.m);
            if (d == 15) {
                self.aluWritePc(result);
            } else {
                self.setReg(d, result);
            }
        }
    }

    fn cmpregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { n: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const n = a.n;
            const r = addWithCarry32(self.getReg(n), ~self.getReg(a.m), true);

            self.psr.n = r.v & 0x8000_0000 != 0;
            self.psr.z = r.v == 0;
            self.psr.c = r.carry_out;
            self.psr.v = r.overflow;
        }
    }

    fn cmpregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { n: u3, m: u4, dn: u1 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const n = (@as(u4, a.dn) << 3) | a.n;
            const r = addWithCarry32(self.getReg(n), ~self.getReg(a.m), true);

            self.psr.n = r.v & 0x8000_0000 != 0;
            self.psr.z = r.v == 0;
            self.psr.c = r.carry_out;
            self.psr.v = r.overflow;
        }
    }

    fn addregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { n: u3, m: u4, dn: u1 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const d = (@as(u4, a.dn) << 3) | a.n;
            const n = d;
            if (d == 0b1101 or a.m == 0b1101) {
                //TODO
                return self.addspregT2();
            }
            const res = addWithCarry32(self.getReg(n), self.getReg(a.m), false);
            if (d == 15) {
                self.aluWritePc(res.v);
            } else {
                self.setReg(d, res.v);
            }
        }
    }

    fn subspimmT1(self: *Cpu) void {
        const imm = ~(@as(u32, @as(u7, @truncate(self.decoder.current))) << 2);
        if (self.conditionPassed()) {
            self.setReg(13, addWithCarry32(self.getReg(13), imm, true).v);
        }
    }

    fn addspimmT2(self: *Cpu) void {
        const imm = @as(u32, @as(u7, @truncate(self.decoder.current))) << 2;
        if (self.conditionPassed()) {
            self.setReg(13, addWithCarry32(self.getReg(13), imm, false).v);
        }
    }

    fn ldrimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, t: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const addr = self.getReg(13) + @as(u32, a.imm) << 2;
            const data = self.readMemU(u32, addr);
            if (a.t == 15) {
                if (addr & 0b11 == 0) {
                    self.loadWritePC(data);
                } else {
                    //unpredicatble
                }
            } else {
                self.setReg(a.t, data);
            }
        }
    }

    fn strimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { imm: u8, t: u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            self.writeMemU(u32, self.getReg(13) + (@as(u32, a.imm) << 2), self.getReg(a.t));
        }
    }

    fn ldrhimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            self.setReg(a.t, self.readMemU(u16, self.getReg(a.n) + @as(u32, a.imm) << 1));
        }
    }

    fn strhimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            self.writeMemU(u16, self.getReg(a.n) + @as(u32, a.imm) << 1, @truncate(self.getReg(a.t)));
        }
    }

    fn ldrbimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            self.setReg(a.t, self.readMemU(u8, self.getReg(a.n) + a.imm));
        }
    }

    fn strbimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            self.writeMemU(u8, self.getReg(a.n) + a.imm, @truncate(self.getReg(a.t)));
        }
    }

    fn ldrimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            const addr = self.getReg(a.n) + @as(u32, a.imm) << 2;
            const data = self.readMemU(u32, addr);
            if (a.t == 15) {
                if (addr & 0b11 == 0) {
                    self.loadWritePC(data);
                } else {
                    //unpredicatble
                }
            } else {
                self.setReg(a.t, data);
            }
        }
    }

    fn strimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
            self.writeMemU(u32, self.getReg(a.n) + (@as(u32, a.imm) << 2), self.getReg(a.t));
        }
    }

    fn ldrregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            const addr = self.getReg(a.n) + self.getReg(a.m);
            const data = self.readMemU(u32, addr);
            if (a.t == 15) {
                if (addr & 0b11 == 0) {
                    self.loadWritePC(data);
                } else {
                    //unpredicatble
                }
            } else {
                self.setReg(a.t, data);
            }
        }
    }

    fn ldrhregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            self.setReg(a.t, self.readMemU(u16, self.getReg(a.n) + self.getReg(a.m)));
        }
    }

    fn ldrbregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            self.setReg(a.t, self.readMemU(u8, self.getReg(a.n) + self.getReg(a.m)));
        }
    }

    fn ldrshregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            self.setReg(a.t, @bitCast(@as(i32, @intCast(@as(i16, @bitCast(self.readMemU(u16, self.getReg(a.n) + self.getReg(a.m))))))));
        }
    }

    fn ldrsbregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            self.setReg(a.t, @bitCast(@as(i32, @intCast(@as(i8, @bitCast(self.readMemU(u8, self.getReg(a.n) + self.getReg(a.m))))))));
        }
    }

    fn strbregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            self.writeMemU(u8, self.getReg(a.n) + self.getReg(a.m), @truncate(self.getReg(a.t)));
        }
    }

    fn strhregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            self.writeMemU(u16, self.getReg(a.n) + self.getReg(a.m), @truncate(self.getReg(a.t)));
        }
    }

    fn strregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            self.writeMemU(u32, self.getReg(a.n) + self.getReg(a.m), self.getReg(a.t));
        }
    }

    fn popT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            var a: u8 = @truncate(self.decoder.current);
            const address = self.getReg(SP_REG);
            const sp = address + ((if (self.decoder.current & 256 > 0)
                bitCount(u8, a) + 1
            else
                bitCount(u8, a)) * 4);
            var addr = self.getReg(SP_REG);
            for (0..8) |i| {
                if (a & 1 > 0) {
                    self.setReg(i, self.readMemA(u32, addr));
                    addr += 4;
                }
                a >>= 1;
            }
            if (self.decoder.current & 256 > 0) {
                self.loadWritePC(self.readMemA(u32, addr));
                addr += 4;
            }
            self.setReg(SP_REG, sp);
            std.debug.assert(addr == self.getReg(SP_REG));
        }
    }

    fn revshT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            var r = self.getReg(a.m);
            const x: i8 = @bitCast(@as([*]u8, @ptrCast(&r))[0]);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..2]);
            r |= (@as(u32, @bitCast(@as(i32, @intCast(x)))) << 8);
            self.setReg(a.d, r);
        }
    }

    fn rev16T1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            var r = self.getReg(a.m);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..2]);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[2..4]);
            self.setReg(a.d, r);
        }
    }

    fn revT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            var r = self.getReg(a.m);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..4]);
            self.setReg(a.d, r);
        }
    }

    fn pushT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            var a: u8 = @truncate(self.decoder.current);
            const address = self.getReg(SP_REG);
            var addr = address - ((if (self.decoder.current & 256 > 0)
                bitCount(u8, a) + 1
            else
                bitCount(u8, a)) * 4);
            const sp = addr;
            for (0..8) |i| {
                if (a & 1 > 0) {
                    self.writeMemA(u32, addr, self.getReg(i));
                    addr += 4;
                }
                a >>= 1;
            }
            if (self.decoder.current & 256 > 0) {
                self.writeMemA(u32, addr, self.getReg(14));
                addr += 4;
            }
            std.debug.assert(addr == self.getReg(SP_REG));
            self.setReg(SP_REG, sp);
        }
    }

    fn uxtbT1(self: *Cpu) void {
        const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
        if (self.conditionPassed()) {
            self.setReg(a.d, //
                @as(u32, //
                @intCast( //
                    @as(u8, //
                        @truncate( //
                            self.getReg(a.m))))));
        }
    }

    fn uxthT1(self: *Cpu) void {
        const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
        if (self.conditionPassed()) {
            self.setReg(a.d, //
                @as(u32, //
                @intCast( //
                    @as(u16, //
                        @truncate( //
                            self.getReg(a.m))))));
        }
    }

    fn sxtbT1(self: *Cpu) void {
        const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
        if (self.conditionPassed()) {
            self.setReg(a.d, //
                @bitCast( //
                @as(i32, //
                    @intCast( //
                        @as(i8, //
                            @bitCast( //
                                @as(u8, //
                                    @truncate( //
                                        self.getReg(a.m)))))))));
        }
    }

    fn sxthT1(self: *Cpu) void {
        const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
        if (self.conditionPassed()) {
            self.setReg(a.d, //
                @bitCast( //
                @as(i32, //
                    @intCast( //
                        @as(i16, //
                            @bitCast( //
                                @as(u16, //
                                    @truncate( //
                                        self.getReg(a.m)))))))));
        }
    }

    fn itinstr(self: *Cpu) void {
        if (@as(u4, @truncate(self.decoder.current)) == 0) {
            //TODO
            unreachable;
        }
        self.psr.setIT(@truncate(self.decoder.current));
    }

    fn cps(self: *Cpu) void {
        if (self.currentModeIsPrivileged()) {
            const a = @as(packed struct(u8) { affectfault: bool, affectpri: bool, z1: bool, z2: bool, disable: bool, r: i3 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            if (!a.disable) {
                if (a.affectpri) self.primask.pm = false;
                if (a.affectfault) self.faultmask.fm = false;
            } else {
                if (a.affectpri) self.primask.pm = true;
                if (a.affectfault and self.execPriortity() > -1) self.faultmask.fm = true;
            }
        }
    }

    fn bT2(self: *Cpu) void {
        const imm: i64 = (@as(*packed struct(u32) { imm: i11, r: u21 }, @ptrCast(&self.decoder.current)).imm << 1);
        self.branchWritePC(@intCast(imm + @as(i64, @intCast(self.getPC()))));
    }

    fn cbzcbnz(self: *Cpu) void {
        const a = @as(packed struct(u16) { rn: u3, imm: u5, eig: u1, i: bool, nine: bool, op: u1, r: u4 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
        const imm3: u32 = @intCast(a.imm << 1);
        if (a.op ^ @intFromBool(self.getReg(a.rn) == 0) > 0) {
            self.branchWritePC(self.getPC() + imm3);
        }
    }

    fn addspregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { bits: u3, rm: u4, bit: u1 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            std.debug.assert(a.bit == 1 and a.bits == 0b101);
            const d = 13;
            //(@as(u32, a.DM) << 3) | a.dm;

            const res = addWithCarry32(self.getReg(SP_REG), self.getReg(a.rm), false);
            self.setReg(d, res.v);
        }
    }

    fn addspregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u8) { dm: u3, bits: u4, bit: u1 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
            std.debug.assert(a.bits == 0b1101);
            const d = (@as(u32, a.DM) << 3) | a.dm;
            const m = d;

            const res = addWithCarry32(self.getReg(SP_REG), self.getReg(m), false);

            if (d == 15) {
                self.aluWritePc(res.v);
            } else {
                self.setReg(d, res.v);
            }
        }
    }

    fn andimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            if (a.rd == 0b1111 and a.s) {
                // TODO goto tstimm
                return self.tstimmT1();
            } else {
                const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
                const result = self.getReg(a.rn) & exp.val;
                self.setReg(a.rd, result);
                if (a.s) {
                    self.psr.n = result & 0x8000_0000 != 0;
                    self.psr.z = result == 0;
                    self.psr.c = exp.carry;
                }
            }
        }
    }

    fn tstimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
            const result = self.getReg(a.rn) & exp.val;
            self.psr.n = result & 0x8000_0000 != 0;
            self.psr.z = result == 0;
            self.psr.c = exp.carry;
        }
    }

    fn bicimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
            const result = self.getReg(a.rn) & ~exp.val;
            self.setReg(a.rd, result);
            if (a.s) {
                self.psr.n = result & 0x8000_0000 != 0;
                self.psr.z = result == 0;
                self.psr.c = exp.carry;
            }
        }
    }

    fn orrimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
            const result = self.getReg(a.rn) | exp.val;
            self.setReg(a.rd, result);
            if (a.s) {
                self.psr.n = result & 0x8000_0000 != 0;
                self.psr.z = result == 0;
                self.psr.c = exp.carry;
            }
        }
    }

    fn movimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
            const result = exp.val;
            self.setReg(a.rd, result);
            if (a.s) {
                self.psr.n = result & 0x8000_0000 != 0;
                self.psr.z = result == 0;
                self.psr.c = exp.carry;
            }
        }
    }

    fn mvnimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
            const result = ~exp.val;
            self.setReg(a.rd, result);
            if (a.s) {
                self.psr.n = result & 0x8000_0000 != 0;
                self.psr.z = result == 0;
                self.psr.c = exp.carry;
            }
        }
    }

    fn ornimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            if (a.rd == 0b1111) {
                // TODO goto tstimm
                return self.mvnimmT1();
            } else {
                const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
                const result = self.getReg(a.rn) & exp.val;
                self.setReg(a.rd, result);
                if (a.s) {
                    self.psr.n = result & 0x8000_0000 != 0;
                    self.psr.z = result == 0;
                    self.psr.c = exp.carry;
                }
            }
        }
    }

    fn teqimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
            const result = self.getReg(a.rn) ^ exp.val;
            self.psr.n = result & 0x8000_0000 != 0;
            self.psr.z = result == 0;
            self.psr.c = exp.carry;
        }
    }

    fn eorimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            if (a.rd == 0b1111 and a.s) {
                // TODO goto tstimm
                return self.teqimmT1();
            } else {
                const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
                const result = self.getReg(a.rn) ^ exp.val;
                self.setReg(a.rd, result);
                if (a.s) {
                    self.psr.n = result & 0x8000_0000 != 0;
                    self.psr.z = result == 0;
                    self.psr.c = exp.carry;
                }
            }
        }
    }

    fn cmnimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = self.thumbExpandImm((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)));
            const result = addWithCarry32(self.getReg(a.rn), exp, false);
            self.psr.n = result.v & 0x8000_0000 != 0;
            self.psr.z = result.v == 0;
            self.psr.c = result.carry_out;
            self.psr.v = result.overflow;
        }
    }

    fn addimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            if (a.rd == 0b1111 and a.s) return self.cmnimmT1();

            if (a.rn == 0b1101) {
                //TODO
                unreachable;
            }

            const exp = self.thumbExpandImm((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)));
            const result = addWithCarry32(self.getReg(a.rn), exp, false);
            self.setReg(a.rd, result.v);
            if (a.s) {
                self.psr.n = result.v & 0x8000_0000 != 0;
                self.psr.z = result.v == 0;
                self.psr.c = result.carry_out;
                self.psr.v = result.overflow;
            }
        }
    }

    fn adcimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const exp = self.thumbExpandImm((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)));
            const result = addWithCarry32(self.getReg(a.rn), exp, self.psr.c);
            self.setReg(a.rd, result.v);
            if (a.s) {
                self.psr.n = result.v & 0x8000_0000 != 0;
                self.psr.z = result.v == 0;
                self.psr.c = result.carry_out;
                self.psr.v = result.overflow;
            }
        }
    }

    fn sbcimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = self.thumbExpandImm((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)));
            const result = addWithCarry32(self.getReg(a.rn), ~exp, self.psr.c);
            self.setReg(a.rd, result.v);
            if (a.s) {
                self.psr.n = result.v & 0x8000_0000 != 0;
                self.psr.z = result.v == 0;
                self.psr.c = result.carry_out;
                self.psr.v = result.overflow;
            }
        }
    }

    fn cmpimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));
            const exp = self.thumbExpandImm((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)));
            const result = addWithCarry32(self.getReg(a.rn), ~exp, true);

            self.psr.n = result.v & 0x8000_0000 != 0;
            self.psr.z = result.v == 0;
            self.psr.c = result.carry_out;
            self.psr.v = result.overflow;
        }
    }

    fn subimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            if (a.rd == 0b1111) return self.cmpimmT2();

            if (a.rn == 0b1101) {
                //TODO
                unreachable;
            }

            const exp = self.thumbExpandImm((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)));
            const result = addWithCarry32(self.getReg(a.rn), ~exp, true);
            self.setReg(a.rd, result.v);
            if (a.s) {
                self.psr.n = result.v & 0x8000_0000 != 0;
                self.psr.z = result.v == 0;
                self.psr.c = result.carry_out;
                self.psr.v = result.overflow;
            }
        }
    }

    fn rsbimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const exp = self.thumbExpandImm((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)));
            const result = addWithCarry32(~self.getReg(a.rn), exp, true);
            self.setReg(a.rd, result.v);
            if (a.s) {
                self.psr.n = result.v & 0x8000_0000 != 0;
                self.psr.z = result.v == 0;
                self.psr.c = result.carry_out;
                self.psr.v = result.overflow;
            }
        }
    }

    fn exec(self: *Cpu, instr: Instr) void {
        std.debug.print("instr: {}\n", .{instr});
        switch (instr) {
            .rsbimmT2 => self.rsbimmT2(),
            .cmpimmT2 => self.cmpimmT2(),
            .subimmT3 => self.subimmT3(),
            .sbcimmT1 => self.sbcimmT1(),
            .adcimmT1 => self.adcimmT1(),
            .addimmT3 => self.addimmT3(),
            .cmnimmT1 => self.cmnimmT1(),
            .eorimmT1 => self.eorimmT1(),
            .teqimmT1 => self.teqimmT1(),
            .ornimmT1 => self.ornimmT1(),
            .mvnimmT1 => self.mvnimmT1(),
            .movimmT2 => self.movimmT2(),
            .orrimmT1 => self.orrimmT1(),
            .bicimmT1 => self.bicimmT1(),
            .tstimmT1 => self.tstimmT1(),
            .andimmT1 => self.andimmT1(),
            //====================
            .ldmT1 => self.ldmT1(),
            .stmT1 => self.stmT1(),
            .addspimmT1 => self.addspimmT1(),
            .adrT1 => self.adrT1(),
            .ldrlitT1 => self.ldrlitT1(),
            .asrT1 => self.asrT1(),
            .lsrT1 => self.lsrT1(),
            .lslT1 => self.lslT1(),
            .addimmT2 => self.addimmT2(),
            .subimmT2 => self.subimmT2(),
            .cmpimmT1 => self.cmpimmT1(),
            .movimmT1 => self.movimmT1(),
            .subimmT1 => subimmT1(self),
            .addimmT1 => addimmT1(self),
            .subregT1 => subregT1(self),
            .addregT1 => addregT1(self),
            .mvnregT1 => mvnregT1(self),
            .bicregT1 => bicregT1(self),
            .mulT1 => mulT1(self),
            .orrregT1 => orrregT1(self),
            .cmnregT1 => cmnregT1(self),
            .rsbimmT1 => rsbimmT1(self),
            .tstregT1 => tstregT1(self),
            .rorregT1 => rorregT1(self),
            .sbcregT1 => sbcregT1(self),
            .adcregT1 => adcregT1(self),
            .asrregT1 => asrregT1(self),
            .lsrregT1 => lsrregT1(self),
            .lslregT1 => lslregT1(self),
            .eorregT1 => eorregT1(self),
            .andregT1 => andregT1(self),
            .blxregT1 => blxregT1(self),
            .bxT1 => bxT1(self),
            .movregT1 => movregT1(self),
            .cmpregT1 => cmpregT1(self),
            .cmpregT2 => cmpregT2(self),
            .addregT2 => addregT2(self),
            .subspimmT1 => subimmT1(self),
            .addspimmT2 => addspimmT2(self),
            .ldrimmT2 => ldrimmT2(self),
            .strimmT2 => strimmT2(self),
            .ldrhimmT1 => ldrhimmT1(self),
            .strhimmT1 => strhimmT1(self),
            .ldrbimmT1 => ldrbimmT1(self),
            .strbimmT1 => strbimmT1(self),
            .ldrimmT1 => ldrimmT1(self),
            .strimmT1 => strimmT1(self),
            .ldrregT1 => ldrregT1(self),
            .ldrhregT1 => ldrhregT1(self),
            .ldrbregT1 => ldrbregT1(self),
            .ldrshregT1 => ldrshregT1(self),
            .ldrsbregT1 => ldrsbregT1(self),
            .strbregT1 => strbregT1(self),
            .strhregT1 => strhregT1(self),
            .strregT1 => strregT1(self),
            .popT1 => popT1(self),
            .revshT1 => revshT1(self),
            .rev16T1 => rev16T1(self),
            .revT1 => revT1(self),
            .pushT1 => pushT1(self),
            .uxtbT1 => uxtbT1(self),
            .uxthT1 => uxthT1(self),
            .sxtbT1 => sxtbT1(self),
            .sxthT1 => sxthT1(self),
            .it => itinstr(self),
            .cps => cps(self),
            .bT2 => bT2(self),
            .cbzcbnz => cbzcbnz(self),
            else => unreachable,
        }

        switch (instr) {
            .it => {},
            else => self.psr.advanceIT(),
        }
    }
};

var cpu = Cpu{};

pub fn main() !void {
    try cpu.init(elf_path);
    for (0..2) |_| {
        const i = try cpu.fetch();
        //std.debug.print("--: {}\n", .{i});
        std.debug.print("last in it: {}\n", .{cpu.psr.getIT().last()});
        cpu.exec(i);
    }
}

pub const Instr = enum { //
    unknown,
    nop,
    yield,
    wfe,
    wfi,
    sev,
    it,
    undefined,
    svc,
    // TODO
    bT1,
    bT2,
    cps,
    addspimmT2,
    subspimmT1,
    cbzcbnz,
    sxthT1,
    sxtbT1,
    uxtbT1,
    uxthT1,
    pushT1,
    revT1,
    rev16T1,
    revshT1,
    popT1,
    strregT1,
    strhregT1,
    strbregT1,
    ldrsbregT1,
    ldrregT1,
    ldrhregT1,
    ldrbregT1,
    ldrshregT1,
    strimmT1,
    ldrimmT1,
    strbimmT1,
    ldrbimmT1,
    strhimmT1,
    ldrhimmT1,
    strimmT2,
    ldrimmT2,
    addregT2,

    cmpregT2,
    //cmpregT1,

    movregT1,
    bxT1,
    blxregT1,

    andregT1,
    eorregT1,
    lslregT1,
    lsrregT1,
    asrregT1,
    adcregT1,
    sbcregT1,
    rorregT1,
    tstregT1,
    rsbimmT1,
    cmpregT1,
    cmnregT1,
    orrregT1,
    mulT1,
    bicregT1,
    mvnregT1,

    addregT1,
    subregT1,
    addimmT1,
    subimmT1,
    lslT1,
    lsrT1,
    asrT1,
    movimmT1,
    cmpimmT1,
    addimmT2,
    subimmT2,

    ldrlitT1,
    adrT1,
    addspimmT1,
    stmT1,
    ldmT1,

    //32 bit
    andimmT1,
    tstimmT1,
    bicimmT1,
    movimmT2,
    orrimmT1,
    mvnimmT1,
    ornimmT1,
    teqimmT1,
    eorimmT1,
    cmnimmT1,
    addimmT3,
    adcimmT1,
    sbcimmT1,
    cmpimmT2,
    subimmT3,
    rsbimmT2,
    //======
    adrT3,
    addimmT4,
    movimmT3,
    adrT2,
    subimmT4,
    movtT1,
    sbfxT1,
    bfcT1,
    bfiT1,
    ubfxT1,
    ssatT1,
    usatT1,

    bT3,
    bT4,
    mrsT1,
    msrT1,
    blT1,

    nopT2,
    yieldT2,
    wfeT2,
    wfiT2,
    sevT2,
    dbgT1,

    clrexT1,
    dsbT1,
    dmbT1,
    isbT1,

    stmT2,
    popT2,
    ldmT2,
    ldmdbT1,
    pushT2,
    stmdbT1,

    strdimmT1,
    ldrdimmT1,
    strexT1,
    ldrexT1,
    strexbT1,
    strexhT1,
    tbbT1,
    ldrexbT1,
    ldrexhT1,

    ldrimmT3,
    ldrimmT4,
    ldrtT1,
    ldrregT2,
    ldrlitT2,

    ldrhimmT2,
    ldrhimmT3,
    ldrhtT1,
    ldrhlitT1,
    ldrhregT2,
    ldrshimmT1,
    ldrshimmT2,
    ldrshtT1,
    ldrshlitT1,
    ldrshregT2,

    ldrbimmT2,
    ldrbimmT3,
    ldrbtT1,
    ldrblitT1,
    ldrbregT2,
    ldrsbimmT1,
    ldrsbT2,
    ldrsbtT1,
    ldrsblitT1,
    ldrsbregT2,
    pldimmT1,

    strbimmT3,
    strbregT2,
    strbimmT2,
    strhimmT2,
    strhimmT3,
    strhregT2,
    strimmT3,
    strimmT4,
    strregT2,

    tstregT2,
    unpredictable,
    andregT2,
    bicregT2,
    orrregT2,
    mvnregT2,
    ornregT1,
    tegregT1,
    eorregT2,
    cmnregT2,
    addregT3,
    adcregT2,
    sbcregT2,
    cmpregT3,
    subregT2,
    rsbregT1,

    movregT3,
    lslimmT2,
    lsrimmT2,
    asrimmT2,
    rrxT1,
    rorimmT1,
};

pub const Decoder = struct {
    const MISC: u32 = 0b1011_0000_0000_0000;
    const COND_BRANCH_SUPERV = 0b1101_0000_0000_0000;
    const UCOND_BRANCH = 0b1110_0000_0000_0000;

    entry: u64,
    stream: std.io.FixedBufferStream([]u8),
    endian: std.builtin.Endian,

    current: u32 = 0,
    current_instr: Instr = .unknown,

    pub fn init(entry: u64, endian: std.builtin.Endian, memory: []u8) !Decoder {
        var self = Decoder{ //
            .endian = endian,
            .entry = entry & 0xffff_ffff_ffff_fffe,
            .stream = std.io.fixedBufferStream(memory),
        };
        try self.stream.seekTo(self.entry);
        return self;
    }

    pub fn reset(self: *Decoder) !void {
        try self.stream.seekTo(self.entry);
    }

    pub fn getWord(self: *Decoder) !u16 {
        return try self.stream.reader().readInt(u16, self.endian);
    }

    fn dataProcModimm32(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u8,
            rd: u4,
            _2: u4,
            rn: u4,
            op: u5,
            _3: u7,
        }, @bitCast(w));

        switch (a.op >> 1) {
            0 => return switch (a.rd) {
                0b1111 => .tstimmT1,
                else => .andimmT1,
            },
            1 => return .bicimmT1,
            2 => return switch (a.rn) {
                0b1111 => .movimmT2,
                else => .orrimmT1,
            },
            3 => return switch (a.rn) {
                0b1111 => .mvnimmT1,
                else => .ornimmT1,
            },
            4 => return switch (a.rd) {
                0b1111 => .teqimmT1,
                else => .eorimmT1,
            },
            8 => return switch (a.rd) {
                0b1111 => .cmnimmT1,
                else => .addimmT3,
            },
            0b1010 => return .adcimmT1,
            0b1011 => return .sbcimmT1,
            0b1101 => return switch (a.rd) {
                0b1111 => .cmpimmT2,
                else => .subimmT3,
            },
            0b1110 => return .rsbimmT2,
            else => return .unknown,
        }
    }

    fn dataProcPB32(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u16,
            rn: u4,
            op: u5,
            _3: u7,
        }, @bitCast(w));

        switch (a.op) {
            0 => return switch (a.rn) {
                0b1111 => .adrT3,
                else => .addimmT4,
            },
            0b100 => return .movimmT3,
            0b1010 => return switch (a.rn) {
                0b1111 => .adrT2,
                else => .subimmT4,
            },
            0b1100 => return .movtT1,
            0b10100 => return .sbfxT1,
            0b10110 => return switch (a.rn) {
                0b1111 => .bfcT1,
                else => .bfiT1,
            },
            0b11100 => return .ubfxT1,
            else => {
                if (a.op >> 2 == 0b100 and a.op & 1 == 0) return .ssatT1;
                if (a.op >> 2 == 0b110 and a.op & 1 == 0) return .usatT1;
                unreachable;
            },
        }

        return .unknown;
    }

    fn hintIntrs(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            op2: u8,
            op1: u3,
            _1: u21,
        }, @bitCast(w));

        if (a.op1 != 0) return .undefined;

        return switch (a.op2) {
            0 => .nopT2,
            1 => .yieldT2,
            2 => .wfeT2,
            3 => .wfiT2,
            4 => .sevT2,
            else => if (a.op2 >> 4 == 0xf) .dbgT1 else unreachable,
        };
    }

    fn miscCtlInstrs(w: u32) Instr {
        const op = (w >> 4) & 0b1111;
        return switch (op) {
            0b10 => .clrexT1,
            0b100 => .dsbT1,
            0b101 => .dmbT1,
            0b110 => .isbT1,
            else => unreachable,
        };
    }

    fn branchMiscCtl32(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u12,
            op2: u3,
            _2: u1,
            _3: u4,
            op1: u7,
            _4: u5,
        }, @bitCast(w));

        switch (a.op2) {
            0 => {
                if (a.op1 & 0b0111000 != 0b0111000) return .bT3;
                if (a.op1 >> 1 == 0b011100) return .msrT1;
                //TODO
                if (a.op1 == 0b0111010) return hintIntrs(w);
                //TODO
                if (a.op1 == 0b0111011) return miscCtlInstrs(w);

                if (a.op1 >> 1 == 0b11111) return .mrsT1;
            },
            else => {
                if (a.op2 == 0b10 and a.op1 == 0b1111111) return .undefined;
                if (a.op2 & 1 == 1 and a.op2 & 0b100 == 0) return .bT4;
                if (a.op2 & 1 == 0 and a.op2 & 0b100 == 0b100) return .undefined;
                if (a.op2 & 1 == 1 and a.op2 & 0b100 == 0b100) return .blT1;
                unreachable;
            },
        }

        return .unknown;
    }

    fn loadStoreMult32(word: u16) Instr {
        const l = (word >> 4) & 1;
        const wrn = (@as(u8, @truncate((word >> 5) & 1)) << 5) | @as(u8, @truncate(word & 0b1111));
        const op = (word >> 7) & 0b11;

        switch (op) {
            0b01 => {
                if (l == 0) return .stmT2;
                if (l == 1 and wrn == 0b11101) return .popT2;
                return .ldmT2;
            },
            0b10 => {
                if (l == 1) return .ldmdbT1;
                if (l == 0 and wrn == 0b11101) return .pushT2;
                return .stmdbT1;
            },
            else => unreachable,
        }
    }

    fn loadStoredualxt32(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u4,
            op3: u4,
            _2: u8,
            //===
            rn: u4,
            op2: u2,
            _3: u1,
            op1: u2,
            _4: u7,
        }, @bitCast(w));

        if ((a.op1 >> 1 == 0 and a.op2 == 0b10) or
            (a.op1 >> 1 == 1 and a.op2 & 1 == 0))
            return .strdimmT1;

        if ((a.op1 >> 1 == 0 and a.op2 == 0b11) or
            (a.op1 >> 1 == 1 and a.op2 & 1 == 1))
            return .ldrdimmT1;

        switch (a.op1) {
            0 => return if (a.op2 == 0) .strexT1 else .ldrexT1,
            1 => return switch (a.op2) {
                0 => switch (a.op3) {
                    0b100 => .strexbT1,
                    0b101 => .strexhT1,
                    else => unreachable,
                },
                1 => switch (a.op3) {
                    0, 1 => .tbbT1,
                    0b100 => .ldrexbT1,
                    0b101 => .ldrexhT1,
                    else => unreachable,
                },
                else => unreachable,
            },
            else => unreachable,
        }
    }

    fn loadword32(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u6,
            op2: u6,
            _2: u4,
            //===
            rn: u4,
            _3: u3,
            op1: u2,
            _4: u7,
        }, @bitCast(w));

        if (a.op1 & 0b10 == 0 and a.rn == 0xf) return .ldrlitT2;

        switch (a.op1) {
            1 => if (a.rn != 0b1111) return .ldrimmT3 else unreachable,
            0 => {
                if (a.op2 & 0b100 != 0 and a.op2 & 0b100000 != 0 and a.rn != 0xf) return .ldrimmT4;
                if (a.op2 >> 2 == 0b1100 and a.rn != 0xf) return .ldrimmT4;
                if (a.op2 >> 2 == 0b1110 and a.rn != 0xf) return .ldrtT1;
                if (a.op2 == 0 and a.rn != 0xf) return .ldrregT2;
                unreachable;
            },
            else => unreachable,
        }
    }

    fn loadhalf32(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u6,
            op2: u6,
            rt: u4,
            //===
            rn: u4,
            _3: u3,
            op1: u2,
            _4: u7,
        }, @bitCast(w));

        if (a.op1 == 1 and a.rn != 0xf and a.rt != 0xf) return .ldrhimmT2;
        if (a.op1 == 0 and a.op2 & 0b100000 != 0 and a.op2 & 0b100 != 0 and a.rn != 0xf and a.rt != 0xf) return .ldrhimmT3;
        if (a.op1 == 0 and a.op2 >> 2 == 0b1100 and a.rn != 0xf and a.rt != 0xf) return .ldrhimmT3;
        if (a.op1 == 0 and a.op2 >> 2 == 0b1110 and a.rn != 0xf and a.rt != 0xf) return .ldrhtT1;
        if (a.op1 & 0b10 == 0 and a.rn == 0xf and a.rt != 0xf) return .ldrhlitT1;
        if (a.op1 == 0 and a.op2 == 0b0 and a.rn != 0xf and a.rt != 0xf) return .ldrhregT2;

        if (a.op1 == 0b11 and a.rn != 0xf and a.rt != 0xf) return .ldrshimmT1;
        if (a.op1 == 0b10 and a.op2 & 0b100000 != 0 and a.op2 & 0b100 != 0 and a.rn != 0xf and a.rt != 0xf) return .ldrshimmT2;
        if (a.op1 == 0b10 and a.op2 >> 2 == 0b1100 and a.rn != 0xf and a.rt != 0xf) return .ldrshimmT2;
        if (a.op1 == 0b10 and a.op2 >> 2 == 0b1110 and a.rn != 0xf and a.rt != 0xf) return .ldrshtT1;

        if (a.op1 & 0b10 != 0 and a.rn == 0xf and a.rt != 0xf) return .ldrshlitT1;
        if (a.op1 == 0b10 and a.op2 == 0 and a.rn != 0xf and a.rt != 0xf) return .ldrshregT2;

        if (a.rt == 0xf) return .nop;

        unreachable;
    }

    fn loadByteMemHints32(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u6,
            op2: u6,
            rt: u4,
            //===
            rn: u4,
            _3: u3,
            op1: u2,
            _4: u7,
        }, @bitCast(w));

        if (a.op1 == 1 and a.rt != 0xf and a.rn != 0xf) return .ldrbimmT2;
        if (a.op1 == 0 and a.op2 & 0b100000 != 0 and a.op2 & 0b100 != 0 and a.rn != 0xf and a.rt != 0xf) return .ldrbimmT3;
        if (a.op1 == 0 and a.op2 >> 2 == 0b1100 and a.rn != 0xf and a.rt != 0xf) return .ldrbimmT3;

        if (a.op1 == 0 and a.op2 >> 2 == 0b1110 and a.rn != 0xf) return .ldrbtT1;

        if (a.op1 & 0b10 == 0 and a.rn == 0xf and a.rt != 0xf) return .ldrblitT1;

        if (a.op1 == 0 and a.op2 == 0 and a.rn != 0xf and a.rt != 0xf) return .ldrbregT2;

        if (a.op1 == 0b11 and a.rt != 0xf and a.rn != 0xf) return .ldrsbimmT1;
        if (a.op1 == 0b10 and a.op2 & 0b100000 != 0 and a.op2 & 0b100 != 0 and a.rn != 0xf and a.rt != 0xf) return .ldrsbT2;
        if (a.op1 == 0b10 and a.op2 >> 2 == 0b1100 and a.rn != 0xf and a.rt != 0xf) return .ldrsbT2;

        if (a.op1 == 0b10 and a.op2 >> 2 == 0b1110 and a.rn != 0xf) return .ldrsbtT1;

        if (a.op1 & 0b10 != 0 and a.rn == 0xf and a.rt != 0xf) return .ldrsblitT1;

        if (a.op1 == 0b10 and a.op2 == 0 and a.rn != 0xf and a.rt != 0xf) return .ldrsbregT2;

        if ((a.op1 == 1 and a.rn != 0xf and a.rt == 0xf) or
            (a.op1 == 0 and a.op2 >> 2 == 0b1100 and a.rn != 0xf and a.rt == 0xf) or
            (a.op1 & 0b10 == 0 and a.rn == 0xf and a.rt == 0xf) or
            (a.op1 == 0 and a.op2 == 0 and a.rn != 0xf and a.rt == 0xf) or
            (a.op1 == 0b11 and a.rn != 0xf and a.rt == 0xf) or
            (a.op1 == 0b10 and a.op2 >> 2 == 0b1100 and a.rn != 0xf and a.rt == 0xf) or
            (a.op1 & 0b10 != 0 and a.rn == 0xf and a.rt == 0xf) or
            (a.op1 == 0b10 and a.op2 == 0 and a.rn != 0xf and a.rt == 0xf))
            //idc
            return .pldimmT1;

        unreachable;
    }

    fn storeSingle32(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u6,
            op2: u6,
            _2: u4,
            //===
            _3: u5,
            op1: u3,
            _4: u8,
        }, @bitCast(w));

        return switch (a.op1) {
            0 => if (a.op2 & 0b100000 != 0) .strbimmT3 else .strbregT2,
            0b100 => .strbimmT2,
            0b101 => .strhimmT2,
            0b1 => if (a.op2 & 0b100000 != 0) .strhimmT3 else .strhregT2,
            0b110 => .strimmT3,
            0b10 => if (a.op2 & 0b100000 != 0) .strimmT4 else .strregT2,
            else => unreachable,
        };
    }

    fn dataProcShiftedReg(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u8,
            rd: u4,
            _2: u4,
            //===
            rn: u4,
            s: bool,
            op: u4,
            _3: u7,
        }, @bitCast(w));

        return switch (a.op) {
            0 => switch (a.rd) {
                0b1111 => if (a.s) .tstregT2 else .unpredictable,
                else => .andregT2,
            },
            1 => .bicregT2,
            0b10 => switch (a.rn) {
                0xf => block: {
                    //Move register and immediate shifts on pageA5-27
                    const b = @as(packed struct(u32) { //
                        _1: u4,
                        type: u2,
                        imm2: u2,
                        _2: u4,
                        imm3: u3,
                        //===
                        _3: u17,
                    }, @bitCast(w));

                    break :block switch (b.type) {
                        0 => if (b.imm3 == 0 and b.imm2 == 0) .movregT3 else .lslimmT2,
                        1 => .lsrimmT2,
                        2 => .asrimmT2,
                        3 => if (b.imm3 == 0 and b.imm2 == 0) .rrxT1 else .rorimmT1,
                    };
                },
                else => .orrregT2,
            },
            0b11 => switch (a.rn) {
                0xf => .mvnregT2,
                else => .ornregT1,
            },
            0b100 => switch (a.rd) {
                0xf => if (a.s) .tegregT1 else .unpredictable,
                else => .eorregT2,
            },
            0b1000 => switch (a.rd) {
                0xf => if (a.s) .cmnregT2 else .unpredictable,
                else => .addregT3,
            },
            0b1010 => .adcregT2,
            0b1011 => .sbcregT2,
            0b1101 => switch (a.rd) {
                0xf => if (a.s) .cmpregT3 else .unpredictable,
                else => .subregT2,
            },
            0b1110 => .rsbregT1,
            else => unreachable,
        };
    }

    fn instr32(self: *Decoder, wh: u16) Instr {
        const wl = @as(u32, self.getWord() catch unreachable);
        self.current = (@as(u32, wh) << 16) | wl;
        if (wh >> 11 == 0b11110 and wh & 0b1000000000 == 0 and wl & 0x8000 == 0) {
            return dataProcModimm32(self.current);
        } else if (wh >> 11 == 0b11110 and wh & 0b1000000000 != 0 and wl & 0x8000 == 0) {
            return dataProcPB32(self.current);
        } else if (wh >> 11 == 0b11110 and wl & 0x8000 != 0) {
            return branchMiscCtl32(self.current);
        } else if (wh >> 9 == 0b1110100 and wh & 0b1000_000 == 0) {
            return loadStoreMult32(wh);
        } else if (wh >> 9 == 0b1110100 and wh & 0b1000_000 != 0) {
            return loadStoredualxt32(self.current);
        } else if (wh >> 9 == 0b1111100 and wh & 0b1000_000 != 0 and wh & 0b10000 != 0) {
            return loadword32(self.current);
        } else if (wh >> 9 == 0b1111100 and ((wh >> 4) & 0b111) == 0b11) {
            return loadhalf32(self.current);
        } else if (wh >> 9 == 0b1111100 and ((wh >> 4) & 0b111) == 0b01) {
            return loadByteMemHints32(self.current);
        } else if (wh >> 8 == 0b11111000 and wh & 0b10000 == 0) {
            return storeSingle32(self.current);
        } else if (wh >> 9 == 0b111_0101) {
            return dataProcShiftedReg(self.current);
        }
        return .unknown;
    }

    pub fn decode(self: *Decoder) !Instr {
        const word = try self.getWord();
        std.debug.print("seq: {b}\n", .{word});
        if (is32bit(word)) {
            return self.instr32(word);
        }

        self.current = @intCast(word);
        self.current_instr = if (word >> 12 == 0b1011)
            misc(word)
        else if (word >> 12 == 0b1101)
            condbrsuperv(word)
        else if (word >> 11 == 0b11100)
            .bT2
        else if (word >> 12 == 0b0101 or //
            word >> 13 == 0b011 or
            word >> 13 == 0b100)
            loadstore(word)
        else if (word >> 10 == 0b10001) specDataBranch(word) else if (word >> 10 == 0b10000) dataProc(word) //
            else if (word >> 14 == 0b00) shaddsubmovcmp(word) else if (word >> 11 == 0b1001) .ldrlitT1 else if (word >> 11 == 0b10101) .addspimmT1 else if (word >> 11 == 0b11000) .stmT1 else if (word >> 11 == 0b11001) .ldmT1 else if (word >> 11 == 0b10100) .adrT1 else unreachable;

        return self.current_instr;
    }

    //0 1 0 0 0 1 0 0

    fn shaddsubmovcmp(word: u16) Instr {
        const opcode = (word >> 9) & 0b11111;
        switch (opcode) {
            0b1100 => return .addregT1,
            0b1101 => return .subregT1,
            0b1110 => return .addimmT1,
            0b1111 => return .subimmT1,
            else => return switch (opcode >> 2) {
                0 => .lslT1,
                1 => .lsrT1,
                2 => .asrT1,
                4 => .movimmT1,
                5 => .cmpimmT1,
                6 => .addimmT2,
                7 => .subimmT2,
                else => unreachable,
            },
        }
        return .unknown;
    }

    fn dataProc(word: u16) Instr {
        const opcode = (word >> 6) & 0b1111;
        return switch (opcode) {
            0 => .andregT1,
            1 => .eorregT1,
            0b10 => .lslregT1,
            0b11 => .lsrregT1,
            0b100 => .asrregT1,
            0b101 => .adcregT1,
            0b110 => .sbcregT1,
            0b111 => .rorregT1,
            0b1000 => .tstregT1,
            0b1001 => .rsbimmT1,
            0b1010 => .cmpregT1,
            0b1011 => .cmnregT1,
            0b1100 => .orrregT1,
            0b1101 => .mulT1,
            0b1110 => .bicregT1,
            0b1111 => .mvnregT1,
            else => unreachable,
        };
    }

    fn specDataBranch(word: u16) Instr {
        const opcode = (word >> 6) & 0b1111;
        if (opcode == 0b100) {
            return Instr.unpredictable;
        } else if (opcode >> 2 == 0) {
            return Instr.addregT2;
        } else if (opcode == 0b101 or opcode >> 1 == 0b11) {
            return Instr.cmpregT2;
        } else if (opcode >> 2 == 0b10) {
            return Instr.movregT1;
        } else if (opcode >> 1 == 0b110) {
            return Instr.bxT1;
        } else if (opcode >> 1 == 0b111) {
            return Instr.blxregT1;
        } else unreachable;
    }

    fn loadstore(word: u16) Instr {
        switch (word >> 9) {
            0b101000 => return .strregT1,
            0b101001 => return .strhregT1,
            0b101010 => return .strbregT1,
            0b101011 => return .ldrsbregT1,
            0b101100 => return .ldrregT1,
            0b101101 => return .ldrhregT1,
            0b101110 => return .ldrbregT1,
            0b101111 => return .ldrshregT1,
            else => switch (word >> 11) {
                0b1100 => return .strimmT1,
                0b1101 => return .ldrimmT1,
                0b1110 => return .strbimmT1,
                0b1111 => return .ldrbimmT1,
                0b10000 => return .strhimmT1,
                0b10001 => return .ldrhimmT1,
                0b10010 => return .strimmT2,
                0b10011 => return .ldrimmT2,
                else => unreachable,
            },
        }
    }

    fn condbrsuperv(word: u16) Instr {
        const op = (word >> 8) & 0b1111;
        return switch (op) {
            0b1110 => .undefined,
            0b1111 => .svc,
            else => .bT1,
        };
    }

    fn misc(word: u16) Instr {
        const opcode = (word >> 5) & 0b1111111;
        if (opcode >> 3 == 0b1111) {
            //std.debug.print("opcode: 0b{b}\n", .{opcode});
            return ifThenHints(word);
        } else if (opcode == 0b110011) {
            return .cps;
        } else if (opcode >> 2 == 0) {
            return .addspimmT2;
        } else if (opcode >> 2 == 1) {
            return .subspimmT1;
        } else if (opcode >> 1 == 0b001000) {
            return .sxthT1;
        } else if (opcode >> 1 == 0b001001) {
            return .sxtbT1;
        } else if (opcode >> 1 == 0b001010) {
            return .uxthT1;
        } else if (opcode >> 1 == 0b001011) {
            return .uxtbT1;
        } else if (opcode >> 1 == 0b101000) {
            return .revT1;
        } else if (opcode >> 1 == 0b101001) {
            return .rev16T1;
        } else if (opcode >> 1 == 0b101011) {
            return .revshT1;
        } else if (opcode >> 4 == 0b010) {
            return .pushT1;
        } else if (opcode >> 4 == 0b110) {
            return .popT1;
        } else if ( //
        opcode >> 3 == 0b0001 or //
            opcode >> 3 == 0b0011 or
            opcode >> 3 == 0b1001 or
            opcode >> 3 == 0b1011)
        {
            return .cbzcbnz;
        }
        return .unknown;
    }

    fn ifThenHints(word: u16) Instr {
        const l = @as(packed struct(u8) { b: u4, a: u4 }, @bitCast(@as(u8, @truncate(word))));
        return switch (l.b) {
            0 => switch (l.a) {
                0 => .nop,
                1 => .yield,
                2 => .wfe,
                3 => .wfi,
                4 => .sev,
                else => unreachable,
            },
            else => .it,
        };
    }

    pub inline fn is32bit(word: u16) bool {
        std.debug.print("word: 0x{x}\n", .{word});
        const mask: u16 = 0b00011000_00000000;
        const mask2: u16 = 0b11100000_00000000;
        if (word & mask == 0) return false;
        return word & mask2 == mask2;
    }
};
