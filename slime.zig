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
    };

    const SP_MAIN = 13;
    const SP_PROC = 15;

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

    fn conditionPassed() bool {
        const cond = currentCondition();
        const res = switch (cond >> 1) {
            0b000 => cpu.psr.z,
            0b001 => cpu.psr.c,
            0b010 => cpu.psr.n,
            0b011 => cpu.psr.v,
            0b100 => cpu.psr.c and cpu.psr.z,
            0b101 => cpu.psr.n == cpu.psr.v,
            0b110 => cpu.psr.n == cpu.psr.v and !cpu.psr.z,
            0b111 => true,
            else => unreachable,
        };

        if ((cond & 1) > 0 and cond != 0b1111) return !res;
        return res;
    }

    fn lookUpSp(self: *const Cpu) usize {
        if (self.control.one) {
            if (self.mode == .thread) return 15;
            return SP_PROC;
        }
        return SP_MAIN;
    }

    fn getReg(self: *Cpu, n: usize) u32 {
        std.debug.assert(n <= 15);
        //if(n <= 15) return self.regs[n];
        if (n == 15) return self.getPC() + 4;
        if (n == 13) return self.regs[self.lookUpSp()];
        return self.regs[n];
    }

    fn setReg(self: *Cpu, n: usize, value: u32) void {
        std.debug.assert(n <= 14);
        if (n == 13) {
            self.regs[self.lookUpSp()] = value;
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
        return @truncate(self.decoder.stream.pos);
    }

    fn getPCOfft(self: *const Cpu) u32 {
        return @truncate(self.decoder.stream.pos + 4);
    }

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

    fn exec(self: *Cpu, instr: Instr) void {
        std.debug.print("instr: {}\n", .{instr});
        switch (instr) {
            .ldrimmT2 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u16) { imm: u8, t:u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
                    //const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
                    const addr = self.getReg(13) + @as(u32,a.imm) << 2;
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
            },
            .strimmT2 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u16) { imm: u8, t:u3, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
                    self.writeMemU(u32, self.getReg(13) + (@as(u32,a.imm) << 2), self.getReg(a.t));
                }
            },
            .ldrhimmT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));

                    //const a = @as(packed struct(u8) { t: u3, n: u3, m: u2}, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.setReg(a.t, self.readMemU(u16, self.getReg(a.n) + @as(u32,a.imm)<<1));
                }
            },
            .strhimmT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));

                    //const a = @as(packed struct(u8) { t: u3, n: u3, m: u2}, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.writeMemU(u16, self.getReg(a.n) + @as(u32,a.imm)<<1, @truncate(self.getReg(a.t)));
                }
            },
            .ldrbimmT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));

                    //const a = @as(packed struct(u8) { t: u3, n: u3, m: u2}, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.setReg(a.t, self.readMemU(u8, self.getReg(a.n) + a.imm));
                }
            },
            .strbimmT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));

                    //const a = @as(packed struct(u8) { t: u3, n: u3, m: u2}, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.writeMemU(u8, self.getReg(a.n) + a.imm, @truncate(self.getReg(a.t)));
                }
            },
            .ldrimmT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
                    const addr = self.getReg(a.n) + @as(u32,a.imm) << 2;
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
            },
            .strimmT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u16) { t: u3, n: u3, imm: u5, r: u5 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
                    self.writeMemU(u32, self.getReg(a.n) + (@as(u32,a.imm) << 2), self.getReg(a.t));
                }
            },
            .ldrregT1 => {
                if (conditionPassed()) {
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
            },
            .ldrhregT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.setReg(a.t, self.readMemU(u16, self.getReg(a.n) + self.getReg(a.m)));
                }
            },
            .ldrbregT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.setReg(a.t, self.readMemU(u8, self.getReg(a.n) + self.getReg(a.m)));
                }
            },
            .ldrshregT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.setReg(a.t, @bitCast(@as(i32, @intCast(@as(i16, @bitCast(self.readMemU(u16, self.getReg(a.n) + self.getReg(a.m))))))));
                }
            },
            .ldrsbregT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.setReg(a.t, @bitCast(@as(i32, @intCast(@as(i8, @bitCast(self.readMemU(u8, self.getReg(a.n) + self.getReg(a.m))))))));
                }
            },
            .strbregT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.writeMemU(u8, self.getReg(a.n) + self.getReg(a.m), @truncate(self.getReg(a.t)));
                }
            },
            .strhregT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.writeMemU(u16, self.getReg(a.n) + self.getReg(a.m), @truncate(self.getReg(a.t)));
                }
            },
            .strregT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { t: u3, n: u3, m: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    self.writeMemU(u32, self.getReg(a.n) + self.getReg(a.m), self.getReg(a.t));
                }
            },
            .popT1 => {
                if (conditionPassed()) {
                    var a: u8 = @truncate(self.decoder.current);
                    const address = self.getReg(self.lookUpSp());
                    const sp = address + ((if (self.decoder.current & 256 > 0)
                        bitCount(u8, a) + 1
                    else
                        bitCount(u8, a)) * 4);
                    var addr = self.getReg(self.lookUpSp());
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
                    self.setReg(self.lookUpSp(), sp);
                    std.debug.assert(addr == self.getReg(self.lookUpSp()));
                }
            },
            .revshT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    var r = self.getReg(a.m);
                    const x: i8 = @bitCast(@as([*]u8, @ptrCast(&r))[0]);
                    std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..2]);
                    r |= (@as(u32, @bitCast(@as(i32, @intCast(x)))) << 8);
                    self.setReg(a.d, r);
                }
            },
            .rev16T1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    var r = self.getReg(a.m);
                    std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..2]);
                    std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[2..4]);
                    self.setReg(a.d, r);
                }
            },
            .revT1 => {
                if (conditionPassed()) {
                    const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                    var r = self.getReg(a.m);
                    std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..4]);
                    self.setReg(a.d, r);
                }
            },
            .pushT1 => {
                if (conditionPassed()) {
                    var a: u8 = @truncate(self.decoder.current);
                    const address = self.getReg(self.lookUpSp());
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
                    std.debug.assert(addr == self.getReg(self.lookUpSp()));
                    self.setReg(self.lookUpSp(), sp);
                }
            },
            .uxtbT1 => {
                const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                if (conditionPassed()) {
                    self.setReg(a.d, //
                        @as(u32, //
                        @intCast( //
                            @as(u8, //
                                @truncate( //
                                    self.getReg(a.m))))));
                }
            },
            .uxthT1 => {
                const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                if (conditionPassed()) {
                    self.setReg(a.d, //
                        @as(u32, //
                        @intCast( //
                            @as(u16, //
                                @truncate( //
                                    self.getReg(a.m))))));
                }
            },
            .sxtbT1 => {
                const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                if (conditionPassed()) {
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
            },
            .sxthT1 => {
                const a = @as(packed struct(u8) { d: u3, m: u3, r: u2 }, @bitCast(@as(u8, @truncate(self.decoder.current))));
                if (conditionPassed()) {
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
            },
            .it => self.psr.setIT(@truncate(self.decoder.current)),
            .cps => {
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
            },
            .bT2 => {
                const imm: i64 = (@as(*packed struct(u32) { imm: i11, r: u21 }, @ptrCast(&self.decoder.current)).imm << 1);
                self.branchWritePC(@intCast(imm + @as(i64, @intCast(self.getPC()))));
            },
            .cbzcbnz => {
                const a = @as(packed struct(u16) { rn: u3, imm: u5, eig: u1, i: bool, nine: bool, op: u1, r: u4 }, @bitCast(@as(u16, @truncate(self.decoder.current))));
                const imm3: u32 = @intCast(a.imm << 1);
                if (a.op ^ @intFromBool(self.getReg(a.rn) == 0) > 0) {
                    self.branchWritePC(self.getPCOfft() + imm3);
                }
            },
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
    bT1,
    bT2,
    bT3,
    cps,
    addT2,
    subT1,
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

    pub fn decode(self: *Decoder) !Instr {
        const word = try self.getWord();
        if (is32bit(word)) @panic("32 bits not handled");
        std.debug.print("seq: {b}\n", .{word});

        self.current = @intCast(word);
        self.current_instr = if (word & MISC == MISC)
            misc(word)
        else if (word & COND_BRANCH_SUPERV == COND_BRANCH_SUPERV)
            condbrsuperv(word)
        else if (word & UCOND_BRANCH == UCOND_BRANCH)
            .bT2
        else if (word >> 12 == 0b0101 or //
            word >> 13 == 0b011 or
            word >> 13 == 0b100)
            loadstore(word)
        else
            unreachable;

        return self.current_instr;
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
            return .addT2;
        } else if (opcode >> 2 == 1) {
            return .subT1;
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

    pub const T16 = struct {
        pub const Shimm = struct {
            pub fn lslimm() void {}
            pub fn lsrimm() void {}
            pub fn asrimm() void {}
            pub fn addreg() void {}
            pub fn subreg() void {}
            pub fn addimm() void {}
            pub fn subimm() void {}
            pub fn add3imm() void {}
            pub fn sub3imm() void {}
            pub fn movimm() void {}
            pub fn compareimm() void {}
            pub fn add8imm() void {}
            pub fn sub8imm() void {}
        };

        pub fn shiftimm(word: u16) void {
            _ = word;
        }

        pub fn dataproc(word: u16) void {
            _ = word;
        }

        pub fn specdatabranx(word: u16) void {
            _ = word;
        }

        pub fn loadflitpl(word: u16) void {
            _ = word;
        }

        pub fn ldstsingle(word: u16) void {
            _ = word;
        }

        pub fn genpcrel(word: u16) void {
            _ = word;
        }

        pub fn gensprel(word: u16) void {
            _ = word;
        }

        pub fn misc(word: u16) void {
            _ = word;
        }

        pub fn stmult(word: u16) void {
            _ = word;
        }

        pub fn ldmult(word: u16) void {
            _ = word;
        }

        pub fn condbrsupv(word: u16) void {
            _ = word;
        }

        pub fn uncondbr(word: u16) void {
            _ = word;
        }
    };

    pub inline fn is32bit(word: u16) bool {
        std.debug.print("word: 0x{x}\n", .{word});
        const mask: u16 = 0b00011000_00000000;
        const mask2: u16 = 0b11100000_00000000;
        if (word & mask == 0) return false;
        return word & mask2 == mask2;
    }
};
