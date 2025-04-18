const std = @import("std");
const elf = std.elf;
const testing = std.testing;

const elf_path = ".\\zig-out\\bin\\code";

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

const Shift = enum(u2) {
    lsl,
    lsr,
    asr,
    ror,
};

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

fn shiftc32(value: u32, t: SRType, amount: u8, carry: bool) ShiftRes {
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

fn shift32(value: u32, t: SRType, amount: u8, carry: bool) u32 {
    // TODO allow overflow
    return shiftc32(value, t, amount, carry).value;
}

fn lslc32(value: u32, n: u8) ShiftRes {
    std.debug.assert(n > 0);
    const res = std.math.shl(u32, value, n - 1);
    const c = res & 0x8000_0000 > 0;
    const ret = ShiftRes{ .value = res << 1, .carry = c };
    return ret;
}

fn lsl32(value: u32, n: u8) u32 {
    if (n == 0) return value;
    return lslc32(value, n).value;
}

test "lsl" {
    try testing.expectEqual(lslc32(1, 1), ShiftRes{ .carry = false, .value = 0b10 });
    try testing.expectEqual(lslc32(1, 32), ShiftRes{ .carry = true, .value = 0b0 });
    try testing.expectEqual(lslc32(1, 31), ShiftRes{ .carry = false, .value = 0x80000000 });
}

fn lsrc32(value: u32, n: u8) ShiftRes {
    std.debug.assert(n > 0);
    //const res = @as(u64, @intCast(value)) >> (n - 1);
    const res = std.math.shr(u32, value, n - 1);
    const c = res & 1 > 0;
    return .{ .value = res >> 1, .carry = c };
}

fn lsr32(value: u32, n: u8) u32 {
    if (n == 0) return value;
    return lsrc32(value, n).value;
}

test "lsr" {
    try testing.expectEqual(lsrc32(1, 1), ShiftRes{ .carry = true, .value = 0b0 });
    try testing.expectEqual(lsrc32(0b10, 1), ShiftRes{ .carry = false, .value = 0b1 });
    try testing.expectEqual(lsrc32(0x80000001, 32), ShiftRes{ .carry = true, .value = 0b0 });
}

fn asrc32(value: u32, n: u8) ShiftRes {
    std.debug.assert(n > 0);
    var res: i64 = @intCast(@as(i32, @bitCast(value)));
    res >>= (@truncate(n - 1));
    const c = res & 1 > 0;
    return .{ .value = @bitCast(@as(i32, @truncate(res >> 1))), .carry = c };
}

fn asr32(value: u32, n: u8) u32 {
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

fn rorc32(value: u32, n: u8) ShiftRes {
    std.debug.assert(n != 0);
    const a = std.math.rotr(u32, value, n);
    //const m = n % 32;
    //lsrc32(value, m).value | lslc32(value, 32 - m).value;
    return .{ .carry = a & 0x80000000 > 0, .value = a };
}

fn ror32(value: u32, n: u8) u32 {
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

const uSAT = struct { result: u32, saturated: bool };
const sSAT = struct { result: i32, saturated: bool };

fn signedSatQ(ii: i32, n: u32) sSAT {
    const i: i64 = @intCast(ii);
    const pow = std.math.pow(i64, 2, @intCast(n - 1));
    return if (i > (pow - 1))
        sSAT{ //
            .result = @truncate(pow - 1),
            .saturated = true,
        }
    else if (i < -(pow))
        sSAT{ //
            .result = @truncate(-pow),
            .saturated = true,
        }
    else
        sSAT{ //
            .result = @bitCast(ii),
            .saturated = false,
        };
}

fn unsignedSatQ(ii: u32, n: u32) uSAT {
    const i: u64 = @intCast(ii);
    const pow = std.math.pow(u64, 2, @intCast(n)) - 1;
    return if (i > (pow)) //
        uSAT{ //
            .result = @truncate(pow),
            .saturated = true,
        }
    else if (i < 0) //
        unreachable
        //uSAT{ //
        //    .result = 0,
        //    .saturated = true,
        //}
    else
        uSAT{ //
            .result = @bitCast(ii),
            .saturated = false,
        };
}

fn signedSat(a: i32, n: u8) i32 {
    return signedSatQ(a, n).result;
}

fn unsignedSat(a: u32, n: u8) u32 {
    return unsignedSatQ(a, n).result;
}

test "satt" {
    try testing.expect(signedSat(1, 1) == 0);
    try testing.expect(signedSat(1, 2) == 1);
    try testing.expect(signedSat(12888, 8) == 127);
    try testing.expect(signedSat(-567, 8) == -128);
    try testing.expect(signedSat(std.math.minInt(i32), 8) == -128);
    try testing.expect(signedSat(std.math.maxInt(i32), 8) == 127);

    try testing.expect(signedSat(std.math.minInt(i32), 32) == std.math.minInt(i32));
    try testing.expect(signedSat(std.math.maxInt(i32), 32) == std.math.maxInt(i32));

    try testing.expect(unsignedSat(260, 8) == 255);
    try testing.expect(unsignedSat(260, 3) == 7);
    try testing.expect(unsignedSat(std.math.maxInt(u32), 32) == std.math.maxInt(u32));
}

const ADC = struct { carry_out: bool, overflow: bool, v: u32 };

fn addWithCarry32(a: u32, b: u32, carry: bool) ADC {
    const un1 = @addWithOverflow(b, @intFromBool(carry));
    const un2 = @addWithOverflow(a, un1[0]);

    const sn1 = @addWithOverflow(@as(i32, @bitCast(b)), @intFromBool(carry));
    const sn2 = @addWithOverflow(@as(i32, @bitCast(a)), sn1[0]);

    return .{ //
        .carry_out = un1[1] == 1 or un2[1] == 1,
        .overflow = sn1[1] == 1 or sn2[1] == 1,
        .v = un2[0],
    };
}

test "sub add" {
    var a: u32 = 3;
    var b: u32 = 1;
    var c: u32 = 2;

    try testing.expect(addWithCarry32(a, ~b, true).v == c);

    a = 3;
    b = 3;
    c = 0;

    try testing.expect(addWithCarry32(a, ~b, true).v == c);

    a = 257;
    b = 257;
    c = 0;

    try testing.expect(addWithCarry32(a, ~b, true).v == c);
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

inline fn onemask(n: u6) u32 {
    return std.math.shl(u32, 0xffff_ffff, n);
}

inline fn zeromask(n: u6) u32 {
    return std.math.shr(u32, 0xffff_ffff, n);
}

fn signExtend(a: u32, n: u6) u32 {
    std.debug.assert(n != 0);
    const signed = a & (@as(u32, 1) << @truncate(n - 1)) != 0;
    if (signed) {
        return a | onemask(@truncate(n));
    }
    return a & zeromask(@truncate(32 - n));
}

test "sextend" {
    try testing.expect(signExtend(1, 1) == 0xffff_ffff);
    try testing.expect(signExtend(1, 2) == 1);
    try testing.expect(signExtend(16, 5) == 0xffff_fff0);
    try testing.expect(signExtend(16, 6) == 16);
}

fn copyBits(to: u32, to_begin: u6, from: u32, from_begin: u6, width: u6) u32 {
    const src_bits = std.math.shl(u32, (std.math.shr(u32, from, from_begin) & zeromask(32 - width)), to_begin);
    const to_top = to & onemask(to_begin + width);
    const to_bottom = to & zeromask(32 - to_begin);
    return to_top | src_bits | to_bottom;
}

test "copy bits" {
    try testing.expectEqual(copyBits(0, 0, 0xf, 0, 4), 0xf);
    try testing.expectEqual(copyBits(0xf000_0000, 0, 0xf, 0, 4), 0xf000_000f);
    try testing.expectEqual(copyBits(0xf000_00fe, 0, 0xf, 0, 1), 0xf000_00ff);
    try testing.expectEqual(copyBits(0x7000_0000, 31, 0x1, 0, 1), 0xf000_0000);
    try testing.expectEqual(copyBits(0xffff_efff, 12, 0x1, 0, 1), 0xffff_ffff);
    try testing.expectEqual(copyBits(0xffff_ffff, 12, 0x0, 0, 4), 0xffff_0fff);
    try testing.expectEqual(copyBits(0xffff_ffff, 0, 0, 0, 32), 0);
}

fn extractBits(from: u32, msbit: u6, lsbit: u6) u32 {
    return std.math.shr(u32, from, lsbit) & zeromask(32 - ((msbit - lsbit) + 1));
}

test "extract bit" {
    try testing.expect(extractBits(1, 0, 0) == 1);
    try testing.expect(extractBits(0b1100, 3, 2) == 0b11);
    try testing.expect(extractBits(0xf000_0000, 31, 28) == 0b1111);
    try testing.expect(extractBits(0xf000_0000, 31, 29) == 0b111);
}

const Cpu = struct {
    const Mode = enum { thread, handler };
    const Exception = enum(u9) { //
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

    /// The Vector table must be naturally aligned to a power of two whose alignment value is greater than or equal
    /// to (Number of Exceptions supported x 4), with a minimum alignment of 128 bytes.T
    fn vectorTableAlignment(exceptions_supported: u32) u32 {
        const x = exceptions_supported * 4;
        if (x > 128) return x;
        return 128;
    }

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
        exception: u9 = 0,
        a: bool = false,
        ici_it3: u2 = 0,
        ici_it2: u4 = 0,
        _res: u8 = 0,
        t: bool = false,
        ici_it: u2 = 0,
        q: bool = false,
        v: bool = false,
        c: bool = false,
        z: bool = false,
        n: bool = false,

        fn getIT(self: *const PSR) ITSTATE {
            return ITSTATE.init(self.ici_it | (@as(u8, self.ici_it3) << 2) | (@as(u8, self.ici_it2) << 4));
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

    const SCS = struct {
        const START = 0xe000e000;
        const STOP = 0xe000efff;
        const Regs = struct {
            const ACTLR = packed struct(u32) {
                const addr = 0xE000E008;
                _1: u32 = 0,
            };
            const CPUID = struct {
                const base_reg_addr = 0xE000ED00;
                const BaseReg = packed struct(u32) { //
                    revision: u4 = 0,
                    partno: u12 = 0,
                    constant: u4 = 0xf,
                    variant: u4 = 0,
                    implementer: u8 = 0,
                };
            };
            const ICSR = packed struct(u32) {
                const addr = 0xE000ED04;

                /// value == 0: Thread mode
                ///  value > 1: the exception numberc for the current executing
                // exception
                vectactive: u9 = 0,
                _1: u1 = 0,
                ///This bit is 1 when the set of all active exceptions minus the
                ///IPSR_current_exception yields the empty set.
                rettobase: bool = false,
                ///Indicates the exception number for the highest priority
                ///pending exception.
                /// value == 0: no pending exceptions
                vectpending: u10 = 0,
                _2: u1 = 0,
                ///Indicates if an external configurable (NVIC generated)
                ///interrupt is pending.
                isrprnding: bool = false,
                /// If set, a pending exception will be serviced on exit from the
                /// debug halt stat
                ispreempt: bool = false,
                _3: u1 = 0,
                /// Clear a pending SysTick (whether set here or by the timer
                /// hardware).
                pendstclr: bool = false,
                /// Set a pending SysTick. Reads back with current state (1 if
                /// Pending, 0 if not).
                pendstset: bool = false,
                /// Clear a pending PendSV interrupt.
                pendsvclr: bool = false,
                /// Set a pending PendSV interrupt. This is normally used to
                /// request a context switch. Reads back with current state (1 if
                /// Pending, 0 if not).
                pendsvset: bool = false,
                _4: u2 = 0,
                /// Setting this bit will activate an NMI. Since NMI is higher
                /// priority than other exceptions, the NMI exception will
                /// activate as soon as it is registered.
                nmipendset: bool = false,
            };
            const VTOR = packed struct(u32) {
                const addr = 0xE000ED08;

                _1: u7 = 0,
                /// Table offset address[28:7] from the base address defined by
                /// TBLBASE.
                ///  The offset address is 32-word aligned. Where more than 16
                /// external interrupts are used, the offset word alignment must be
                /// increased to accommodate vectors for all the exceptions and
                /// interrupts supported and keep the required table size naturally
                /// aligned. See Interrupt Controller Type Register (ICTR) on
                /// page B3-32 for information on the number of interrupts
                /// supported.
                tbloff: u22 = 0,
                ///
                /// value ==0: Table base is in CODE, base address 0x00000000
                ///value ==1: Table base is in RAM, base address 0x20000000
                tblbase_is_ram: bool = false,
                _2: u2 = 0,
            };
            const AIRCR = packed struct(u32) {
                const addr = 0xE000ED0C;
                /// Local system reset, see Reset management on
                /// page B1-47 for details. This bit self-clears.
                /// Writing a 1 to this bit when not in debug state (halted) is
                /// UNPREDICTABLE.
                ///  If VECTRESET and SYSRESETREQ are set
                /// simultaneously, the behavior is UNPREDICTABLE.
                vectreset: bool = false,
                /// Clears all active state information for fixed and
                /// configurable exceptions. This bit self-clears.
                /// Note: It is the application’s responsibility to re-initialize
                /// the stack.
                ///  Writing a 1 to this bit when not in debug state (halted) is
                /// UNPREDICTABLE.
                vectclractive: bool = false,
                /// Writing this bit 1 will cause a signal to be asserted to the
                /// external system to indicate a reset is requested. The
                /// signal is required to generate a Local Reset.
                ///  The bit self-clears as part of the reset sequence.
                sysresetreq: bool = false,
                _2: u5 = 0,
                /// Priority grouping position (binary point). This field sets
                /// the interpretation of priority registers, both for handlers
                /// and standard interrupts. For a definition of how this bit
                /// field is interpreted to assign priority and priority
                /// sub-group bit fields to the System Handler and NVIC
                /// priority registers, see Priority grouping on page B1-18)
                ///  This field is cleared on reset.
                prigroup: u3 = 0,
                _3: u4 = 0,
                big_endian: bool = false,
                vectkey_vectkeystat: u16 = 0,

                inline fn vectkeystat() u16 {
                    return 0xfa05;
                }
            };
            const SCR = packed struct(u32) {
                const addr = 0xE000ED10;

                _1: bool = false,
                /// When enabled,  interrupt transitions from Inactive to
                /// Pending are included in the list of wakeup events for the WFE
                /// instruction.
                ///  See WFE wake-up events on page B1-49 for more
                /// information.
                sleeponexit: bool = false,
                /// A qualifying hint that indicates waking from sleep might
                /// take longer. Implementations can take advantage of the
                /// feature to identify a lower power sleep state.
                sleepdeep: bool = false,
                _2: bool = false,

                ///  When enabled,  interrupt transitions from Inactive to
                /// Pending are included in the list of wakeup events for the WFE
                /// instruction.
                ///  See WFE wake-up events on page B1-49 for more
                /// information.
                sevonpend: bool = false,
                _3: u27 = 0,
            };
            const CCR = packed struct(u32) {
                const addr = 0xE000ED14;

                /// 0 (default): Thread state can only be entered at the
                /// Base level of activation (will fault if attempted to
                /// another level of activation).
                ///  1: Thread state can be entered at any level by
                /// controlled return value. See Exception return
                /// behavior on page B1-25 for details.
                nonebasethrdena: bool = false,
                /// When this bit is set (=1), the core allows unprivileged
                /// (user) code to write the Software Trigger Interrupt
                /// register. See Software Trigger Interrupt Register
                /// (STIR) on page B3-23.
                usersetmpend: bool = false,
                _1: u1 = 0,
                /// Enable bit (=1) for trapping unaligned half or full
                /// word accessesa
                unalign_trp: bool = false,
                /// Enable bit (=1) for trap on Divide by 0.
                div0trp: bool = false,
                _2: u3 = 0,
                /// When enabled (=1), this causes handlers running at
                /// priority -1 and -2 to ignore Precise data access faults.
                /// When disabled (=0), these bus faults will cause a
                /// lock-up as explained in Unrecoverable exception
                /// cases on page B1-44.
                bfhfnmign: bool = false,
                /// 1: on exception entry, the SP used prior to the
                /// exception is adjusted to be 8-byte aligned and the
                /// context to restore it is saved. The SP is restored on the
                /// associated exception return.
                ///  0: only 4-byte alignment is guaranteed for the SP used
                /// prior to the exception on exception entry.
                ///  The bit is cleared on reset. See Stack alignment on
                /// exception entry on page B1-24 for more information.
                stackalign: bool = false,
                _3: u22 = 0,
            };
            const SHPR1 = packed struct(u32) {
                const addr = 0xE000ED18;
                pri4: u8 = 0,
                pri5: u8 = 0,
                pri6: u8 = 0,
                pri7: u8 = 0,
            };
            const SHPR2 = packed struct(u32) {
                const addr = 0xE000ED1C;

                pri8: u8 = 0,
                pri9: u8 = 0,
                pri10: u8 = 0,
                pri11: u8 = 0,
            };
            const SHPR3 = packed struct(u32) {
                const addr = 0xE000ED20;
                pri12: u8 = 0,
                pri13: u8 = 0,
                pri14: u8 = 0,
                pri15: u8 = 0,
            };
            const SHCSR = packed struct(u32) {
                const addr = 0xE000ED24;

                memfaultact: bool = false,
                busfaultact: bool = false,
                _1: bool = false,
                usgfaultact: bool = false,
                _2: u3 = 0,
                svccallact: bool = false,
                monitoract: bool = false,
                _3: u1 = 0,
                pendsvact: bool = false,
                systickact: bool = false,
                usgfaultpended: bool = false,
                memfaultpended: bool = false,
                busfaultpended: bool = false,
                svccallpended: bool = false,
                memfaultena: bool = false,
                busfaultena: bool = false,
                usgfaultena: bool = false,
                _4: u13 = 0,
            };
            const CFSR = packed struct(u32) {
                const addr = 0xE000ED28;

                const MemManage = packed struct(u8) {
                    const addr = 0xE000ED28;

                    /// MPU or eXecuteNever (XN) default memory map access
                    /// violation on an instruction fetch. The fault is only signalled
                    /// if the instruction is issued.
                    iaccviol: bool = false,
                    /// Data access violation. The MMAR is set to the data address
                    /// which the load/store tried to access.
                    daccviol: bool = false,
                    _1: u1 = 0,
                    /// A derived MemManage fault has occurred on exception
                    /// return.
                    munstkerr: bool = false,
                    /// A derived MemManage fault has occurred on exception
                    /// entry.
                    mstkerr: bool = false,
                    _2: u2 = 0,
                    /// This bit is set if the MMAR register has valid contents
                    mmarvalid: bool = false,
                };

                const BusFault = packed struct(u8) {
                    const addr = 0xE000ED29;

                    /// This bit indicates a bus fault on an instruction prefetch. The
                    /// fault is only signalled if the instruction is issued.
                    ibuserr: bool = false,
                    /// Precise data access error. The BFAR is written with the
                    /// faulting address.
                    preciserr: bool = false,
                    /// Imprecise data access error.
                    impreciserr: bool = false,
                    /// This bit indicates a derived bus fault has occurred on
                    /// exception return.
                    unstkerr: bool = false,
                    /// This bit indicates a derived bus fault has occurred on
                    /// exception entry.
                    stkerr: bool = false,
                    _1: u2 = 0,
                    ///  This bit is set if the BFAR register has valid contents.
                    bfarvalid: bool = false,
                };

                const UsageFault = packed struct(u16) {
                    const addr = 0xE000ED2A;

                    /// Undefined instruction executed (including those associated
                    /// with an enabled Coprocessor).
                    undefinstr: bool = false,
                    /// Invalid EPSR.T bit or illegal EPSR.IT bits for executing
                    /// instruction
                    invstate: bool = false,
                    /// Integrity check error on EXC_RETURN.
                    invpc: bool = false,
                    /// Coprocessor access error (the coprocessor is disabled or not
                    /// present)
                    nocp: bool = false,
                    _1: u4 = 0,
                    /// Unaligned access error. Multi-word accesses always fault if
                    /// not word aligned. Unaligned word and halfwords can be
                    /// configured to fault (UNALIGN_TRP is enabled)
                    unaligned: bool = false,
                    /// Divide by zero error. When SDIV or UDIV instruction is used
                    /// with a divisor of 0, this fault will occur if DIV_0_TRP is
                    /// enabled.
                    divbyzero: bool = false,
                    _2: u6 = 0,
                };

                mem_manage: MemManage = .{},
                bus_fault: BusFault = .{},
                usage_fault: UsageFault = .{},
            };
            const HFSR = packed struct(u32) {
                const addr = 0xE000ED2C;
                _1: u1 = 0,
                /// Fault was due to vector table read on exception processing.
                vecttbl: bool = false,
                _2: u28 = 0,
                /// Configurable fault cannot be activated due to priority or
                /// because it is disabled. Priority escalated to a HardFault
                /// exception.
                ///  See Priority escalation on page B1-19.
                forced: bool = false,
                /// Debug event, and the Debug Fault Status Register has been
                /// updated. Only set when halting debug is disabled
                /// (C_DEBUGEN = 0) See Debug event behavior on
                /// page C1-14 for more information
                debugevt: bool = false,
            };
            const DFSR = packed struct(u32) {
                const addr = 0xE000ED30;
                _1: u32 = 0,
            };
            const AFSR = packed struct(u32) {
                const addr = 0xE000ED3C;
                _1: u32 = 0,
            };
            const MMFAR = packed struct(u32) {
                const addr = 0xE000ED34;
                /// Data address MPU faulted. This is the location which a load or
                /// store attempted to access which was faulted. The MemManage
                /// Status Register provides the cause, and indicates if the content of
                /// this register is valid.When an unaligned access faults, the address
                /// will be the actual address which faulted; since an access may be
                /// split into multiple parts (each aligned), this address therefore may
                /// be any offset in the range of the requested size.
                address: u32 = 0,
            };

            const BFAR = packed struct(u32) {
                const addr = 0xE000ED38;
                /// Updated on precise data access faults. The value is the faulting
                /// address associated with the attempted access. The BusFault Status
                /// Register provides information on the reason, and indicates if the
                /// content of this register is valid.For unaligned access faults, the
                /// address is the address requested by the instruction, which is not
                /// necessarily the address which faulted.
                address: u32 = 0,
            };
            const CPACR = packed struct(u32) {
                const addr = 0xE000ED88;
                cpacr: u32 = 0,
            };

            const PID4 = packed struct(u32) {
                const addr = 0xE000EFD0;
                _1: u32 = 0,
            };
            const PID5 = packed struct(u32) {
                const addr = 0xE000EFD4;
                _1: u32 = 0,
            };
            const PID6 = packed struct(u32) {
                const addr = 0xE000EFD8;
                _1: u32 = 0,
            };
            const PID7 = packed struct(u32) {
                const addr = 0xE000EFDC;
                _1: u32 = 0,
            };
            const PID0 = packed struct(u32) {
                const addr = 0xE000EFE0;
                _1: u32 = 0,
            };
            const PID1 = packed struct(u32) {
                const addr = 0xE000EFE4;
                _1: u32 = 0,
            };
            const PID2 = packed struct(u32) {
                const addr = 0xE000EFE8;
                _1: u32 = 0,
            };
            const PID3 = packed struct(u32) {
                const addr = 0xE000EFEC;
                _1: u32 = 0,
            };

            const CID0 = packed struct(u32) {
                const addr = 0xE000EFF0;
                _1: u32 = 0,
            };
            const CID1 = packed struct(u32) {
                const addr = 0xE000EFF4;
                _1: u32 = 0,
            };
            const CID2 = packed struct(u32) {
                const addr = 0xE000EFF8;
                _1: u32 = 0,
            };
            const CID3 = packed struct(u32) {
                const addr = 0xE000EFFC;
                _1: u32 = 0,
            };

            const SysTick = struct {
                const SYST_CSR = packed struct(u32) {
                    const addr = 0xE000E010;
                    /// 0: the counter is disabled
                    ///  1: the counter will operate in a multi-shot manner.
                    enable: bool,
                    /// If 1, counting down to 0 will cause the SysTick exception to
                    /// be pended. Clearing the SysTick Current Value register by a
                    /// register write in software will not cause SysTick to be
                    /// pended.
                    tickint: bool,
                    /// 0: clock source is (optional) external reference clock
                    ///  1: core clock used for SysTick
                    ///  If no external clock provided, this bit will read as 1 and
                    /// ignore writes.
                    clcksource: bool,
                    _1: u13,
                    /// Returns 1 if timer counted to 0 since last time this register
                    /// was read. COUNTFLAG is set by a count transition from 1
                    /// => 0. COUNTFLAG is cleared on read or by a write to the
                    /// Current Value register.
                    countflag: bool,
                    _2: u15,
                };

                const SYST_RVR = packed struct(u32) {
                    const addr = 0xE000E014;
                    /// Value to load into the Current Value register when the counter
                    /// reaches 0.
                    reload: u24,
                    _1: u8,
                };

                const SYST_CVR = packed struct(u32) {
                    const addr = 0xE000E018;
                    /// Current counter value. This is the value of the counter at the time
                    /// it is sampled. The counter does not provide read-modify-write
                    /// protection.The register is write-clear. A software write of any
                    /// value will clear the register to 0. Unsupported bits RAZ (see
                    /// SysTick Reload Value register).
                    current: u32,
                };

                const SYST_CALIB = packed struct(u32) {
                    const addr = 0xE000E01C;
                    /// An optional Reload value to be used for 10ms (100Hz) timing,
                    /// subject to system clock skew errors. If the value reads as 0, the
                    /// calibration value is not known.
                    tenms: u24,
                    _1: u6,
                    /// If reads as 1, the calibration value for 10ms is inexact (due to clock
                    /// frequency).
                    skew: bool,
                    /// If reads as 1, the Reference clock is not provided – the
                    /// CLKSOURCE bit of the SysTick Control and Status register will
                    /// be forced to 1 and cannot be cleared to 0.
                    noref: bool,
                };
            };

            const NVIC = struct {
                const STIR = packed struct(u32) {
                    const addr = 0xE000EF00;
                    /// The value written in this field is the interrupt to be triggered. This
                    /// acts the same as storing to the corresponding ISPR[x] set-pending
                    /// NVIC register bit. See Interrupt Set-Pending and Clear-Pending
                    /// Registers (NVIC_ISPRx and NVIC_ICPRx) on page B3-33.
                    ///  This register applies to external interrupts only. The value written is
                    /// (ExceptionNumber - 16), see Exception number definition on
                    /// page B1-16.
                    intid: u9 = 0,
                    _1: u23 = 0,
                };

                const ICTR = packed struct(u32) {
                    const addr = 0xE000E004;
                    /// Number of interrupt lines supported by NVIC in
                    /// granularities of 32.
                    intlinesnum: u4 = 0,
                    _1: u28 = 0,

                    fn getIntlines(self: ICTR) u32 {
                        return (self.intlinesnum * 32) + 32;
                    }
                };

                const NVIC_ISER = packed struct(u32) {
                    const addr = 0xE000E100;
                    /// Enable one or more interrupts within a group of 32. Each bit
                    /// represents an interrupt number from N to N+31 (starting at
                    /// interrupt 0, 32, 64, etc).
                    /// Writing a 1 will enable the associated interrupt.
                    /// Writing a 0 has no effect.
                    /// The register reads back with the current enable state.
                    setena: u32 = 0,
                };

                const NVIC_ICER = packed struct(u32) {
                    const addr = 0xE000E180;
                    /// Disable one or more interrupts within a group of 32. Each bit
                    /// represents an interrupt number from N to N+31 (starting at
                    /// interrupt 0, 32, 64, etc).
                    /// Writing a 1 will disable the associated interrupt.
                    ///  Writing a 0 has no effect.
                    ///  The register reads back with the current enable state.
                    clrena: u32 = 0,
                };

                const NVIC_ISPR = packed struct(u32) {
                    const addr = 0xE000E200;

                    ///  Writing a 1 to a bit pends the associated interrupt under software
                    /// control. Each bit represents an interrupt number from N to N+31
                    /// (starting at interrupt 0, 32, 64, etc).
                    /// Writing a 0 to a bit has no effect on the associated interrupt.The
                    /// register reads back with the current pending state.
                    setpend: u32 = 0,
                };

                const NVIC_ICPR = packed struct(u32) {
                    const addr = 0xE000E280;
                    /// Writing a 1 to a bit un-pends the associated interrupt under
                    /// software control. Each bit represents an interrupt number from N
                    /// to N+31 (starting at interrupt 0, 32, 64, etc).
                    /// Writing a 0 to a bit has no effect on the associated interrupt.
                    ///  The register reads back with the current pending state.
                    clrpend: u32 = 0,
                };

                const NVIC_IABR = packed struct(u32) {
                    const addr = 0xE000E300;
                    /// Each bit represents the current active state for the associated
                    /// interrupt within a group of 32. Each bit represents an interrupt
                    /// number from N to N+31 (starting at interrupt 0, 32, 64, etc).
                    active: u32 = 0,
                };

                const NVIC_IPR = packed struct(u32) {
                    const addr = 0xE000E400;
                    /// Priority of interrupt number N (0, 4, 8, etc).
                    pri_n: u8 = 0,
                    /// Priority of interrupt number N+1 (1, 5, 9, etc).
                    pri_n1: u8 = 0,
                    /// Priority of interrupt number N+2 (2, 6, 10, etc).
                    pri_n2: u8 = 0,
                    /// Priority of interrupt number N+3 (3, 7, 11, etc).
                    pri_n3: u8 = 0,
                };
            };
        };
    };

    const SAM = struct {
        const MB4: u32 = 1024 * 1024 * 4;
        const Map = struct { begin: u32, end: u32, realbegin: u32 };

        const code = Map{ //
            .begin = 0x00000000,
            .realbegin = 0,
            .end = 0x1FFFFFFF,
        };
        const sram = Map{ //
            .begin = 0x20000000,
            .realbegin = MB4,
            .end = 0x3FFFFFFF,
        };
        const peripheral = Map{ //
            .begin = 0x40000000,
            .realbegin = MB4 * 2,
            .end = 0x5FFFFFFF,
        };
        const ram0 = Map{ //
            .begin = 0x60000000,
            .end = 0x7FFFFFFF,
            .realbegin = MB4 * 3,
        };
        const ram1 = Map{ //
            .begin = 0x80000000,
            .end = 0x9FFFFFFF,
            .realbegin = MB4 * 4,
        };
        const device_shared = Map{ //
            .begin = 0xA0000000,
            .end = 0xBFFFFFFF,
            .realbegin = MB4 * 5,
        };
        const device_nonshared = Map{ //
            .begin = 0xC0000000,
            .end = 0xDFFFFFFF,
            .realbegin = MB4 * 6,
        };
        const system = Map{ //
            .begin = 0xE0000000,
            .end = 0xFFFFFFFF,
            .realbegin = MB4 * 7,
        };
    };

    // offset in 4 bytes
    fn readMemMappedReg(self: *Cpu, T: type, offset: u32) T {
        if (@hasDecl(T, "addr")) {
            const reg = self.readMemA(u32, T.addr + (offset * 4));
            return @bitCast(reg);
        } else @compileError(std.fmt.comptimePrint("{s} has no addr decr.\n", .{@typeName(T)}));
    }

    // offset in 4 bytes
    fn writeMemMappedReg(self: *Cpu, T: type, value: T, offset: u32) void {
        if (@hasDecl(T, "addr")) {
            self.writeMemA(u32, T.addr + (offset * 4), @bitCast(value));
        } else @compileError(std.fmt.comptimePrint("{s} has no addr field.\n", .{@typeName(T)}));
    }

    fn resetSCSRegs(self: *Cpu) void {
        _ = self;
        //TODO
    }

    fn updateSCSRegs(self: *Cpu) void {
        _ = self;
        //TODO
    }

    fn clearExclusiveLocal(self: *Cpu) void {
        _ = self;
        //TODO
    }

    fn clearEventRegister(self: *Cpu) void {
        _ = self;
        //TODO
    }

    fn returnAddress(self: *Cpu) u32 {
        //TODO
        return self.PC;
    }

    fn setEventRegister(self: *Cpu) void {
        _ = self;
        //TODO
    }

    fn instructionSyncBarrier(self: *Cpu) void {
        _ = self;
        //TODO
    }

    fn pushStack(self: *Cpu) void {
        const ccr = self.readMemMappedReg(SCS.Regs.CCR, 0);
        const curr_sp = if (self.control.one and self.getMode() == .thread)
            self.regs[SP_PROC] //
        else
            self.regs[SP_MAIN];

        const frameptralign = ((curr_sp & 0b10) > 0) and ccr.stackalign;
        const frameptr = (curr_sp - 0x20) & ~@as(u32, if (ccr.stackalign) 0b100 else 0);

        self.writeMemA(u32, frameptr, self.getReg(0));
        self.writeMemA(u32, frameptr + 4, self.getReg(1));
        self.writeMemA(u32, frameptr + 8, self.getReg(2));
        self.writeMemA(u32, frameptr + 12, self.getReg(3));
        self.writeMemA(u32, frameptr + 16, self.getReg(12));
        self.writeMemA(u32, frameptr + 20, self.getRL());
        self.writeMemA(u32, frameptr + 24, self.returnAddress());
        var psr = self.psr;
        psr.a = frameptralign;
        self.writeMemA(u32, frameptr + 28, @bitCast(psr));

        if (self.getMode() == .handler) {
            self.setRL(0xffff_fff1);
        } else {
            if (self.control.one) {
                self.setRL(0xffff_fffd);
            } else {
                self.setRL(0xffff_fff9);
            }
        }
    }

    fn exceptionTaken(self: *Cpu, exept: u9) void {
        const vector_table: u32 = @bitCast(self.readMemMappedReg(SCS.Regs.VTOR, 0));
        const tmp = self.readMemA(u32, vector_table + 4 * exept);
        self.PC = tmp & 0xffff_fffe;
        self.setMode(.handler);
        self.psr.exception = exept;
        self.psr.t = (tmp & 1) == 1;
        self.psr.setIT(0);
        self.control.one = false;
        self.exception_active[exept] = 1;
        //TODO
        self.updateSCSRegs();
        self.clearExclusiveLocal();
        self.setEventRegister();
        self.instructionSyncBarrier();
    }

    fn exceptionActiveBitCount(self: *Cpu) u32 {
        var res: u32 = 0;
        for (self.exception_active[0..]) |e| {
            if (e == 1) res += 1;
        }
        return res;
    }

    fn deActivate(self: *Cpu, returning_excpt: u9) void {
        self.exception_active[returning_excpt] = 0;
        if (self.psr.exception != 0b10) {
            self.faultmask.fm = false;
        }
    }

    fn popStack(self: *Cpu, frameptr: u32, excret: u4) void {
        self.setReg(0, self.readMemA(u32, frameptr));
        self.setReg(1, self.readMemA(u32, frameptr + 4));
        self.setReg(2, self.readMemA(u32, frameptr + 8));
        self.setReg(3, self.readMemA(u32, frameptr + 12));
        self.setReg(12, self.readMemA(u32, frameptr + 16));
        self.setRL(self.readMemA(u32, frameptr + 20));
        self.setPC(self.readMemA(u32, frameptr + 24));
        self.psr = @bitCast(self.readMemA(u32, frameptr + 28));

        const ccr = self.readMemMappedReg(SCS.Regs.CCR, 0);

        var stkln: u32 = if (ccr.stackalign) 0b1 else 0;
        if (self.psr.a) stkln &= 1 else stkln &= 0;
        stkln <<= 2;
        switch (excret) {
            0b1, 0b1001 => self.regs[SP_MAIN] = (self.regs[SP_MAIN] + 0x20) | stkln,
            0b1101 => self.regs[SP_PROC] = (self.regs[SP_PROC] + 0x20) | stkln,
            else => unreachable,
        }
    }

    fn exceptionReturn(self: *Cpu, exc_ret: u28) void {
        const nested_activation = self.exceptionActiveBitCount();

        if (self.getMode() != .handler) {
            std.debug.print("FATAL: exception return in thread mode!!!. Reseting...\n", .{});
            self.takeReset();
        }
        const returning_exception_number = self.psr.exception;

        var cfsr = self.readMemMappedReg(SCS.Regs.CFSR, 0);
        const ccr = self.readMemMappedReg(SCS.Regs.CCR, 0);
        var frame_ptr: u32 = undefined;

        if (self.exception_active[returning_exception_number] == 0) {
            self.deActivate(returning_exception_number);
            cfsr.usage_fault.invpc = true;
            self.writeMemMappedReg(SCS.Regs.CFSR, cfsr, 0);
            self.setRL(0xf000_0000 + exc_ret);
            self.exceptionTaken(@intFromEnum(Exception.usagefault));
            return;
        }
        switch (exc_ret & 0b1111) {
            1 => {
                if (nested_activation == 1) {
                    self.deActivate(returning_exception_number);
                    cfsr.usage_fault.invpc = true;
                    self.writeMemMappedReg(SCS.Regs.CFSR, cfsr, 0);
                    self.setRL(0xf000_0000 + exc_ret);
                    self.exceptionTaken(@intFromEnum(Exception.usagefault));
                    return;
                }
                frame_ptr = self.regs[SP_MAIN];
                self.setMode(.handler);
                self.control.one = false;
            },
            0b1001, 0b1101 => |v| {
                if (nested_activation != 1 and !ccr.nonebasethrdena) {
                    self.deActivate(returning_exception_number);
                    cfsr.usage_fault.invpc = true;
                    self.writeMemMappedReg(SCS.Regs.CFSR, cfsr, 0);
                    self.setRL(0xf000_0000 + exc_ret);
                    self.exceptionTaken(@intFromEnum(Exception.usagefault));
                    return;
                }
                frame_ptr = self.regs[if (v == 0b1001) SP_MAIN else SP_PROC];
                self.setMode(.thread);
                self.control.one = false;
            },
            else => {
                self.deActivate(returning_exception_number);
                cfsr.usage_fault.invpc = true;
                self.writeMemMappedReg(SCS.Regs.CFSR, cfsr, 0);
                self.setRL(0xf000_0000 + exc_ret);
                self.exceptionTaken(@intFromEnum(Exception.usagefault));
                return;
            },
        }

        self.deActivate(returning_exception_number);
        self.popStack(frame_ptr, @truncate(exc_ret));

        if (self.getMode() == .handler and self.psr.exception == 0) {
            self.deActivate(returning_exception_number);
            cfsr.usage_fault.invpc = true;
            self.writeMemMappedReg(SCS.Regs.CFSR, cfsr, 0);
            self.pushStack();
            self.setRL(0xf000_0000 + exc_ret);
            self.exceptionTaken(@intFromEnum(Exception.usagefault));
            return;
        }

        if (self.getMode() == .thread and self.psr.exception != 0) {
            self.deActivate(returning_exception_number);
            cfsr.usage_fault.invpc = true;
            self.writeMemMappedReg(SCS.Regs.CFSR, cfsr, 0);
            self.pushStack();
            self.setRL(0xf000_0000 + exc_ret);
            self.exceptionTaken(@intFromEnum(Exception.usagefault));
            return;
        }
    }

    fn takeReset(self: *Cpu) void {
        var vector_table: u32 = @bitCast(self.readMemMappedReg(SCS.Regs.VTOR, 0));
        vector_table &= 0x3fff_ff80;

        self.regs[SP_MAIN] = vector_table & 0xffff_fffc;
        self.regs[SP_PROC] = 0;

        self.setRL(0xffff_ffff);
        const tmp = self.readMemA(u32, vector_table + 4);
        self.PC = tmp & 0xffff_fffe;
        self.psr.t = (tmp & 1) == 1;
        self.psr.setIT(0);
        self.primask.pm = false;
        self.faultmask.fm = false;
        self.basepri.basepri = 0;
        self.control.zero = false;
        self.control.one = false;
        self.resetSCSRegs();
        for (0..self.exception_active.len) |i| {
            self.exception_active[i] = 0;
        }
        self.clearExclusiveLocal();
        self.clearEventRegister();
    }

    memory: []u8 = undefined,
    mem_steam: std.io.FixedBufferStream([]u8) = undefined,

    exception_active: [512]u8 = [1]u8{0} ** 512,

    regs: [16]u32 = [1]u32{0} ** 16,
    psr: PSR = PSR{},
    primask: PRIMASK = .{},
    faultmask: FAULTMASK = .{},
    basepri: BASEPRI = .{},
    decoder: Decoder = undefined,
    mode: Mode = .thread,
    control: CONTROL = CONTROL{},

    PC: u32 = 0,

    fn currentModeIsPrivileged(self: *Cpu) bool {
        return switch (self.getMode()) {
            .handler => true,
            else => return self.control.zero,
        };
    }

    fn getExecutionPriority(self: *Cpu) i32 {
        _ = self;
        return 0;
    }

    fn getMode(self: *Cpu) Mode {
        return self.mode;
    }

    fn setMode(self: *Cpu, mode: Mode) void {
        self.mode = mode;
    }

    fn loadElf(
        self: *Cpu,
        path: []const u8,
    ) !void {
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

        self.decoder.endian = elf_header.endian;
        //TODO
        self.PC = @truncate(elf_header.entry & 0xffff_ffff_ffff_fffe);
        //try Decoder.init(elf_header.entry, elf_header.endian, self.memory[0..]);

        //std.debug.print("***PC***: 0x{x} (0x{x})\n", .{ self.getPC(), self.decoder.stream.pos });
    }

    fn printRegisters(self: *Cpu) void {
        //std.debug.print("============BEGIN==============\n", .{});
        for (0..16) |i| {
            if (i == 8) std.debug.print("\n", .{});
            if (i == 15 or i == 14) {
                std.debug.print("   r{}: {x} ", .{ i, self.getReg(i) - 4 });
            } else {
                std.debug.print("   r{}: {} ", .{ i, self.getReg(i) });
            }
        }

        std.debug.print("\n", .{});

        std.debug.print("   Z: {} ", .{self.psr.z});
        std.debug.print("   C: {} ", .{self.psr.c});
        std.debug.print("   V: {} ", .{self.psr.v});
        std.debug.print("   N: {} ", .{self.psr.n});
        std.debug.print("   Q: {} ", .{self.psr.q});
        std.debug.print("   T: {} ", .{self.psr.t});
        std.debug.print("   A: {} \n", .{self.psr.a});
        //std.debug.print("============BEGIN==============\n", .{});

    }

    fn setAndExecCurrentInstr(self: *Cpu, instr: Instr, current: u32) void {
        self.decoder.current = current;
        self.decoder.current_instr = instr;
        self.exec(instr);
    }

    fn init(self: *Cpu, mem: []u8) !void {
        self.memory = mem;

        self.mode = .thread;
        self.control = .{};

        self.basepri = .{};
        self.primask = .{};
        self.faultmask = .{};

        self.psr = .{ .t = true };

        self.mem_steam = std.io.fixedBufferStream(self.memory[0..]);
        self.decoder = try Decoder.init(.big, self.memory[0..]);

        self.regs = [1]u32{0} ** 16;
    }

    fn exclusiveMonitorsPass(self: *Cpu, addr: u32, n: u32) bool {
        _ = self;
        _ = addr;
        _ = n;
        return true;
    }

    fn setExclusiveMonitors(self: *Cpu, address: u32, n: u32) void {
        _ = address;
        _ = n;
        _ = self;
    }

    fn currentCondition(self: *Cpu) u4 {
        switch (self.decoder.current_instr) {
            .bT1 => {
                const cond: u4 = @truncate(((self.decoder.current >> 8) & 0b1111));
                return cond;
            },
            .bT3 => {
                return @truncate((self.decoder.current >> 22) & 0b1111);
            },
            else => {
                const it = self.psr.getIT();
                return if (it.in())
                    self.psr.getIT().cond()
                else
                    0b1111;
            },
        }
    }

    fn integerZeroDivideTrappingEnabled(self: *Cpu) bool {
        _ = self;
        //TODO
        return false;
    }

    fn thumbExpandImm(self: *Cpu, bits: u12) u32 {
        return thumbExpandImmC(bits, self.psr.c).val;
    }

    fn conditionPassed(self: *Cpu) bool {
        const cond = self.currentCondition();
        const res = switch (cond >> 1) {
            0b000 => self.psr.z,
            0b001 => self.psr.c,
            0b010 => self.psr.n,
            0b011 => self.psr.v,
            0b100 => self.psr.c and !self.psr.z,
            0b101 => self.psr.n == self.psr.v,
            0b110 => self.psr.n == self.psr.v and !self.psr.z,
            0b111 => true,
            else => unreachable,
        };

        if ((cond & 1) > 0 and cond != 0b1111) {
            return !res;
        }
        return res;
    }

    fn _lookUpSp(self: *const Cpu) usize {
        if (self.control.one) {
            if (self.mode == .thread) return 15;
            return SP_PROC;
        }
        return SP_MAIN;
    }

    fn getReg(self: *const Cpu, n: usize) u32 {
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

    ///pc = addr
    fn branchTo(self: *Cpu, addr: u32) void {
        self.setPC(@intCast(addr));
    }

    ///branch to addr & 0xfffffffe
    fn branchWritePC(self: *Cpu, addr: u32) void {
        self.branchTo(addr & 0xfffffffe);
    }

    ///branch to addr & 0xfffffffe set psr.t
    fn bxWrtePC(self: *Cpu, addr: u32) void {
        if (self.getMode() == .handler and (addr & 0xf000_0000) == 0xf000_0000) {
            //TODO
            @panic("unhandled case!!");
        } else {
            self.psr.t = addr & 1 == 1;
            self.branchTo(addr & 0xffff_fffe);
        }
    }

    ///branch to addr & 0xfffffffe set psr.t if frst bit
    fn loadWritePC(self: *Cpu, addr: u32) void {
        self.bxWrtePC(addr);
    }

    ///branch to addr & 0xfffffffe
    fn aluWritePc(self: *Cpu, addr: u32) void {
        self.branchWritePC(addr);
    }

    fn getPC(self: *const Cpu) u32 {
        return @truncate((self.PC + 4) % self.memory.len);
    }

    fn getRL(self: *const Cpu) u32 {
        return self.getReg(14);
    }

    fn setRL(self: *Cpu, v: u32) void {
        self.setReg(14, v);
    }

    // use in exec loop
    fn setPC(self: *Cpu, ip: u32) void {
        //for inrecment at bottom
        if (self.decoder.on32) {
            self.PC = ip - 4;
        } else {
            self.PC = ip - 2;
        }
    }

    fn execPriortity(self: *Cpu) i8 {
        _ = self;
        return 0;
    }

    fn translateAddress(self: *Cpu, addr: u32) u32 {
        _ = self;
        const MAP_SIZE = SAM.MB4;
        if (addr >= SAM.code.begin and addr < (SAM.code.begin + MAP_SIZE)) {
            return (addr - SAM.code.begin) + SAM.code.realbegin;
        } else if (addr >= SAM.device_nonshared.begin and addr < (SAM.device_nonshared.begin + MAP_SIZE)) {
            return (addr - SAM.device_nonshared.begin) + SAM.device_nonshared.realbegin;
        } else if (addr >= SAM.device_shared.begin and addr < (SAM.device_shared.begin + MAP_SIZE)) {
            return (addr - SAM.device_shared.begin) + SAM.device_shared.realbegin;
        } else if (addr >= SAM.ram0.begin and addr < (SAM.ram0.begin + MAP_SIZE)) {
            return (addr - SAM.ram0.begin) + SAM.ram0.realbegin;
        } else if (addr >= SAM.ram1.begin and addr < (SAM.ram1.begin + MAP_SIZE)) {
            return (addr - SAM.ram1.begin) + SAM.ram1.realbegin;
        } else if (addr >= SAM.sram.begin and addr < (SAM.sram.begin + MAP_SIZE)) {
            return (addr - SAM.sram.begin) + SAM.sram.realbegin;
        } else if (addr >= SAM.peripheral.begin and addr < (SAM.peripheral.begin + MAP_SIZE)) {
            return (addr - SAM.peripheral.begin) + SAM.peripheral.realbegin;
        } else if (addr >= SAM.system.begin and addr < (SAM.system.begin + MAP_SIZE)) {
            return (addr - SAM.system.begin) + SAM.system.realbegin;
        }

        //TODO raise busfault
        unreachable;
    }

    fn fetch(self: *Cpu) Instr {
        return self.decoder.decode(self.translateAddress(self.PC));
    }

    fn readMemA(self: *Cpu, T: type, addrz: u32) T {
        const addr = self.translateAddress(addrz);
        if (addr % @sizeOf(T) != 0) @panic("unaligned mem access!!");
        self.mem_steam.seekTo(addr % self.memory.len) catch unreachable;
        //TODO check endian
        return self.mem_steam.reader().readInt(T, self.decoder.endian) catch unreachable;
    }

    fn writeMemA(self: *Cpu, T: type, addrz: u32, val: T) void {
        const addr = self.translateAddress(addrz);
        if (addr % @sizeOf(T) != 0) @panic("unaligned mem access!!");
        self.mem_steam.seekTo(addr % self.memory.len) catch unreachable;
        //TODO check endian
        self.mem_steam.writer().writeInt(T, val, self.decoder.endian) catch unreachable;
    }

    fn readMemU(self: *Cpu, T: type, addrz: u32) T {
        const addr = self.translateAddress(addrz);
        self.mem_steam.seekTo(addr % self.memory.len) catch unreachable;
        //TODO check endian
        return self.mem_steam.reader().readInt(T, self.decoder.endian) catch unreachable;
    }

    fn writeMemU(self: *Cpu, T: type, addrz: u32, val: T) void {
        const addr = self.translateAddress(addrz);
        self.mem_steam.seekTo(addr % self.memory.len) catch unreachable;
        //TODO check endian
        self.mem_steam.writer().writeInt(T, val, self.decoder.endian) catch unreachable;
    }

    fn readMemA_Unpriv(self: *Cpu, T: type, addrz: u32) T {
        const addr = self.translateAddress(addrz);
        if (addr % @sizeOf(T) != 0) @panic("unaligned mem access!!");
        self.mem_steam.seekTo(addr % self.memory.len) catch unreachable;
        //TODO check endian
        return self.mem_steam.reader().readInt(T, self.decoder.endian) catch unreachable;
    }

    fn writeMemA_Unpriv(self: *Cpu, T: type, addrz: u32, val: T) void {
        const addr = self.translateAddress(addrz);
        if (addr % @sizeOf(T) != 0) @panic("unaligned mem access!!");
        self.mem_steam.seekTo(addr % self.memory.len) catch unreachable;
        //TODO check endian
        self.mem_steam.writer().writeInt(T, val, self.decoder.endian) catch unreachable;
    }

    fn readMemU_Unpriv(self: *Cpu, T: type, addrz: u32) T {
        const addr = self.translateAddress(addrz);
        self.mem_steam.seekTo(addr % self.memory.len) catch unreachable;
        //TODO check endian
        return self.mem_steam.reader().readInt(T, self.decoder.endian) catch unreachable;
    }

    fn writeMemU_Unpriv(self: *Cpu, T: type, addrz: u32, val: T) void {
        const addr = self.translateAddress(addrz);
        self.mem_steam.seekTo(addr % self.memory.len) catch unreachable;
        //TODO check endian
        self.mem_steam.writer().writeInt(T, val, self.decoder.endian) catch unreachable;
    }

    fn ldmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rn: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            var bits = a.imm8;
            var address = self.getReg(a.rn);
            var wback = false;
            for (0..8) |i| {
                if (bits & 1 == 1) {
                    self.setReg(i, self.readMemA(u32, address));
                    address += 4;
                } else {
                    if (i == a.rn) wback = true;
                }
                bits >>= 1;
            }
            if (wback) self.setReg(a.rn, address);
        }
    }

    test "ldmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm8: u8,
            rn: u3,
            _1: u21,
        });
        a.imm8 = 0xff;
        try cpu.mem_steam.seekTo(0);
        for (0..8) |i| {
            try cpu.mem_steam.writer().writeInt(u32, @truncate(i), .big);
        }

        cpu.setAndExecCurrentInstr(.ldmT1, @bitCast(a));

        for (0..8) |i| {
            try std.testing.expect(cpu.getReg(i) == i);
        }

        a.imm8 = 0xfe;
        try cpu.mem_steam.seekTo(0);
        for (0..8) |i| {
            try cpu.mem_steam.writer().writeInt(u32, @truncate(i), .big);
        }

        cpu.setReg(a.rn, 0);
        cpu.setAndExecCurrentInstr(.ldmT1, @bitCast(a));

        for (0..8) |i| {
            if (i == a.rn) {
                try std.testing.expect(cpu.getReg(i) == (7 * 4));
            } else {
                try std.testing.expect(cpu.getReg(i) == i - 1);
            }
        }
    }

    fn stmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm: u8,
                n: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
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

    test "stmT1" {}

    fn addspimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm: u8,
                rd: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rd, self.getReg(SP_REG) + (@as(u32, a.imm) << 2));
        }
    }

    test "addspimmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm: u8,
            rd: u3,
            _1: u21,
        });
        a.rd = 4;
        a.imm = 56;
        cpu.setReg(SP_REG, 60);
        cpu.setAndExecCurrentInstr(.addspimmT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == (60 + (56 << 2)));
    }

    fn adrT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm: u8,
                rd: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const r = std.mem.alignBackward(u32, self.getPC(), 4) + (@as(u32, a.imm) << 2);
            self.setReg(a.rd, r);
        }
    }

    test "adrT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm: u8,
            rd: u3,
            _1: u21,
        });

        a.imm = 4;
        cpu.PC = 0;

        cpu.setAndExecCurrentInstr(.adrT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 20);
    }

    fn ldrlitT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm: u8,
                t: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const addr = std.mem.alignBackward(u32, self.getPC(), 4) + (@as(u32, a.imm) << 2);
            const data = self.readMemU(u32, addr);
            self.setReg(a.t, data);
        }
    }

    test ldrlitT1 {
        //pass
    }

    fn asrimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                imm5: u5,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const r = shiftc32(self.getReg(a.rm), .asr, @intCast(a.imm5), self.psr.c);
            self.setReg(a.rd, r.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.value & 0x8000_0000 != 0;
                self.psr.z = r.value == 0;
                self.psr.c = r.carry;
            }
        }
    }

    test "asrimmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rd: u3,
            rm: u3,
            imm5: u5,
            _1: u21,
        });

        a.rd = 0;
        a.rm = 1;
        a.imm5 = 1;
        cpu.setReg(a.rm, 0x8000_0000);
        cpu.setAndExecCurrentInstr(.asrimmT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xc000_0000);
        try testing.expect(cpu.psr.n);
    }

    fn lsrimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                imm5: u5,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const r = shiftc32(self.getReg(a.rm), .lsr, @intCast(a.imm5), self.psr.c);
            self.setReg(a.rd, r.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.value & 0x8000_0000 != 0;
                self.psr.z = r.value == 0;
                self.psr.c = r.carry;
            }
        }
    }

    test lsrimmT1 {}

    fn lslimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                imm5: u5,
                _1: u21,
            }, @bitCast(self.decoder.current));
            //TODO remove shif32
            const r = shiftc32(self.getReg(a.rm), .lsl, @intCast(a.imm5), self.psr.c);
            self.setReg(a.rd, r.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.value & 0x8000_0000 != 0;
                self.psr.z = r.value == 0;
                self.psr.c = r.carry;
            }
        }
    }

    test lslimmT1 {}

    fn addimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rdn: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const r = addWithCarry32(self.getReg(a.rdn), a.imm8, false);
            self.setReg(a.rdn, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    test "addimmT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm8: u8,
            rdn: u3,
            _1: u21,
        });
        a.imm8 = 90;
        cpu.setReg(a.rdn, 90);
        cpu.setAndExecCurrentInstr(.addimmT2, @bitCast(a));
        try testing.expect(cpu.getReg(a.rdn) == 180);
    }

    fn subimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rdn: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const r = addWithCarry32(self.getReg(a.rdn), ~@as(u32, a.imm8), true);
            self.setReg(a.rdn, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    test subimmT2 {}

    fn cmpimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rn: u3,
                r: u21,
            }, @bitCast(self.decoder.current));

            const r = addWithCarry32(self.getReg(a.rn), ~@as(u32, a.imm8), true);

            self.psr.n = r.v & 0x8000_0000 != 0;
            self.psr.z = r.v == 0;
            self.psr.c = r.carry_out;
            self.psr.v = r.overflow;
        }
    }

    test "cmpimmT1" {
        //pass
    }

    fn movimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm: u8,
                d: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const r: u32 = a.imm;
            self.setReg(a.d, r);
            if (!self.psr.getIT().in()) {
                self.psr.n = r & 0x8000_0000 != 0;
                self.psr.z = r == 0;
            }
        }
    }

    test movimmT1 {}

    fn subimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rn: u3,
                rm: u3,
                r: u23,
            }, @bitCast(self.decoder.current));
            const r = addWithCarry32(self.getReg(a.rn), ~@as(u32, a.rm), true);
            self.setReg(a.rd, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    test "subimmT1" {}

    fn addimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rn: u3,
                imm3: u3,
                r: u23,
            }, @bitCast(self.decoder.current));
            const r = addWithCarry32(self.getReg(a.rn), a.imm3, false);
            self.setReg(a.rd, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    test "addimmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rd: u3,
            rn: u3,
            imm3: u3,
            r: u23,
        });

        a.rd = 1;

        cpu.setAndExecCurrentInstr(.addimmT1, @bitCast(a));
        try testing.expect(cpu.psr.z);

        cpu.psr.z = false;
        cpu.psr.setITALL();
        cpu.setAndExecCurrentInstr(.addimmT1, @bitCast(a));
        try testing.expect(!cpu.psr.z);
    }

    fn subregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rn: u3,
                rm: u3,
                _: u23,
            }, @bitCast(self.decoder.current));
            const r = addWithCarry32(self.getReg(a.rn), ~self.getReg(a.rm), true);
            self.setReg(a.rd, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    test subregT1 {}

    fn addregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rn: u3,
                rm: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));
            const r = addWithCarry32(self.getReg(a.rn), self.getReg(a.rm), false);
            self.setReg(a.rd, r.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = r.v & 0x8000_0000 != 0;
                self.psr.z = r.v == 0;
                self.psr.c = r.carry_out;
                self.psr.v = r.overflow;
            }
        }
    }

    test "addregT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rd: u3,
            rn: u3,
            rm: u3,
            _: u23,
        });

        a.rm = 1;

        cpu.setReg(0, 50);
        cpu.setReg(1, 51);

        cpu.setAndExecCurrentInstr(.addregT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 101);
    }

    fn mvnregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = ~self.getReg(a.rm);
            self.setReg(a.rdn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    test mvnregT1 {}

    fn bicregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = ~self.getReg(a.rm) & self.getReg(a.rdn);
            self.setReg(a.rdn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    test "bicregT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rdn: u3,
            rm: u3,
            _1: u26,
        });

        a.rdn = 1;
        cpu.setReg(a.rm, 0xff);
        cpu.setReg(a.rdn, 0xfff);
        cpu.setAndExecCurrentInstr(.bicregT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rdn) == 0xf00);
    }

    fn mulT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = self.getReg(a.rm) * self.getReg(a.rdn);
            self.setReg(a.rdn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    test "mulT1" {}

    fn orrregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = self.getReg(a.rm) | self.getReg(a.rdn);
            self.setReg(a.rdn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    test "orrregT1" {}

    fn cmnregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));

            const r = addWithCarry32(self.getReg(a.rn), self.getReg(a.rm), false);

            self.psr.n = r.v & 0x8000_0000 != 0;
            self.psr.z = r.v == 0;
            self.psr.c = r.carry_out;
            self.psr.v = r.overflow;
        }
    }

    test "cmnregT1" {
        //
    }

    fn rsbimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rn: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = addWithCarry32(~self.getReg(a.rn), 0, true);
            self.setReg(a.rd, res.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    test "rsbimmT1" {}

    fn tstregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = self.getReg(a.rm) & self.getReg(a.rn);
            self.psr.n = res & 0x8000_0000 != 0;
            self.psr.z = res == 0;
        }
    }

    test tstregT1 {}

    fn rorregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const shift_n: u8 = @truncate(self.getReg(a.rm) & 0xff);
            const res = shiftc32(self.getReg(a.rdn), .ror, shift_n, self.psr.c);
            self.setReg(a.rdn, res.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test "rorregT1" {}

    fn sbcregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = addWithCarry32(self.getReg(a.rdn), ~self.getReg(a.rm), self.psr.c);
            self.setReg(a.rdn, res.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    test "sbcregT1" {}

    fn adcregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = addWithCarry32(self.getReg(a.rdn), self.getReg(a.rm), self.psr.c);
            self.setReg(a.rdn, res.v);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    test "adcregT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rdn: u3,
            rm: u3,
            _1: u26,
        });

        cpu.psr.c = true;
        a.rm = 1;
        a.rdn = 0;

        cpu.setAndExecCurrentInstr(.adcregT1, @bitCast(a));
        try testing.expect(cpu.getReg(0) == 1);

        cpu.psr.c = false;
        cpu.psr.setIT(0xff);

        cpu.setReg(1, std.math.maxInt(u32));
        cpu.setAndExecCurrentInstr(.adcregT1, @bitCast(a));

        try testing.expect(cpu.psr.c == false);
        try testing.expect(cpu.psr.z == false);

        cpu.psr.c = true;
        cpu.psr.setIT(0x0);

        cpu.setReg(1, std.math.maxInt(u32));
        cpu.setAndExecCurrentInstr(.adcregT1, @bitCast(a));

        try testing.expect(cpu.psr.c == true);
        try testing.expect(cpu.psr.z == true);

        cpu.psr.c = true;
        cpu.psr.setIT(0x0);

        cpu.setReg(1, std.math.maxInt(u32) - 1);
        cpu.setAndExecCurrentInstr(.adcregT1, @bitCast(a));

        try testing.expect(cpu.psr.n == true);
    }

    fn asrregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const shift_n: u6 = @intCast(self.getReg(a.rm) & 0xff);
            const res = shiftc32(self.getReg(a.rdn), .asr, shift_n, self.psr.c);
            self.setReg(a.rdn, res.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test "asrregT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rdn: u3,
            rm: u3,
            _1: u26,
        });
        a.rdn = 0;
        a.rm = 2;
        cpu.setReg(a.rm, 0xf00f);
        cpu.setReg(a.rdn, 0x8000_0000);
        cpu.setAndExecCurrentInstr(.asrregT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rdn) == 0xffff_0000);
    }

    fn lsrregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const shift_n: u6 = @truncate(self.getReg(a.rm) & 0xff);
            const res = shiftc32(self.getReg(a.rdn), .lsr, shift_n, self.psr.c);
            self.setReg(a.rdn, res.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test lsrregT1 {}

    fn lslregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _0: u26,
            }, @bitCast(self.decoder.current));
            const shift_n: u6 = @truncate(self.getReg(a.rm) & 0xff);
            const res = shiftc32(self.getReg(a.rdn), .lsl, shift_n, self.psr.c);
            self.setReg(a.rdn, res.value);
            if (!self.psr.getIT().in()) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test lslregT1 {}

    fn eorregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = self.getReg(a.rm) ^ self.getReg(a.rdn);
            self.setReg(a.rdn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    test "eorregT1" {
        //pass
    }

    fn andregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const res = self.getReg(a.rm) & self.getReg(a.rdn);
            self.setReg(a.rdn, res);
            if (!self.psr.getIT().in()) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
            }
        }
    }

    test "andregT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rdn: u3,
            rm: u3,
            _1: u26,
        });

        a.rdn = 1;
        a.rm = 0;

        cpu.setReg(a.rdn, 0xf);
        cpu.setReg(a.rm, 0xf);
        cpu.setAndExecCurrentInstr(.andregT1, @bitCast(a));

        try testing.expect(cpu.getReg(a.rdn) == 0xf);
    }

    fn blxregT1(self: *Cpu) void {
        //TODO rause exception
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                d: u3,
                m: u4,
                _1: u25,
            }, @bitCast(self.decoder.current));
            const target = self.getReg(a.m);
            self.setRL((self.getPC() - 2) | 1);
            self.bxWrtePC(target);
        }
    }

    test "blxregT1" {
        //not used in m3
    }

    fn bxT1(self: *Cpu) void {
        //TODO raise exeption
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                _1: u3,
                m: u4,
                _2: u25,
            }, @bitCast(self.decoder.current));
            self.bxWrtePC(self.getReg(a.m));
        }
    }

    test "bxT1" {
        // not used
    }

    //same with lsl #0
    fn movregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const d = a.d;
            const r = self.getReg(a.rm);

            self.setReg(d, r);
            self.psr.n = r & 0x8000_0000 != 0;
            self.psr.z = r == 0;
        }
    }

    test movregT2 {}

    fn movregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u4,
                D: u1,
                _1: u24,
            }, @bitCast(self.decoder.current));
            const d = (@as(u4, a.D) << 3) | a.rd;
            const result = self.getReg(a.rm);
            if (d == 15) {
                self.aluWritePc(result);
            } else {
                self.setReg(d, result);
            }
        }
    }

    test movregT1 {}

    fn cmpregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rn: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            const r = addWithCarry32(self.getReg(a.rn), ~self.getReg(a.rm), true);
            self.psr.n = r.v & 0x8000_0000 != 0;
            self.psr.z = r.v == 0;
            self.psr.c = r.carry_out;
            self.psr.v = r.overflow;
        }
    }

    test "cmpregT1" {
        //pass
    }

    fn cmpregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rn: u3,
                rm: u4,
                N: u1,
                _1: u24,
            }, @bitCast(self.decoder.current));
            const n = (@as(u4, a.N) << 3) | a.rn;
            const r = addWithCarry32(self.getReg(n), ~self.getReg(a.rm), true);

            self.psr.n = r.v & 0x8000_0000 != 0;
            self.psr.z = r.v == 0;
            self.psr.c = r.carry_out;
            self.psr.v = r.overflow;
        }
    }

    test "cmpregT2" {
        //
    }

    fn addregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rdn: u3,
                rm: u4,
                DN: u1,
                _1: u24,
            }, @bitCast(self.decoder.current));
            const d = (@as(u4, a.DN) << 3) | a.rdn;
            const n = d;
            const res = addWithCarry32(self.getReg(n), self.getReg(a.rm), false);
            if (d == 15) {
                self.aluWritePc(res.v);
            } else {
                self.setReg(d, res.v);
            }
        }
    }

    test "addregT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rdn: u3,
            rm: u4,
            DN: u1,
            _1: u24,
        });

        a.rdn = 0b111;
        a.DN = 1;
        cpu.decoder.on32 = false;
        cpu.setReg(a.rm, 0b1111);
        cpu.PC = 10;
        cpu.setAndExecCurrentInstr(.addregT2, @bitCast(a));
        // added to PC+4
        try testing.expect(cpu.PC == 0b1110 + 4 + 10);
    }

    fn subspimmT1(self: *Cpu) void {
        const imm = @as(u32, @as(u7, @truncate(self.decoder.current))) << 2;
        if (self.conditionPassed()) {
            self.setReg(13, addWithCarry32(self.getReg(13), ~imm, true).v);
        }
    }

    test subspimmT1 {}

    fn addspimmT2(self: *Cpu) void {
        const imm = @as(u32, @as(u7, @truncate(self.decoder.current))) << 2;
        if (self.conditionPassed()) {
            self.setReg(SP_REG, self.getReg(SP_REG) + imm);
        }
    }

    test "addspimmT2" {
        try cpu.init(mem_buf[0..]);
        cpu.setReg(SP_REG, 40);
        cpu.setAndExecCurrentInstr(.addspimmT2, 40);
        try testing.expect(cpu.getReg(SP_REG) == 200);
    }

    fn ldrimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm: u8,
                t: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(13) + (@as(u32, a.imm) << 2);
            const data = self.readMemU(u32, addr);
            self.setReg(a.t, data);
        }
    }

    test "ldrimmT2" {
        //pass
    }

    fn strimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm: u8,
                t: u3,
                _1: u21,
            }, @bitCast(self.decoder.current));
            self.writeMemU(u32, self.getReg(13) + (@as(u32, a.imm) << 2), self.getReg(a.t));
        }
    }

    test "strimmT2" {}

    fn ldrhimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                imm5: u5,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const addr = (self.getReg(a.rn) + (@as(u32, a.imm5) << 1));
            self.setReg(a.rt, self.readMemU(u16, addr));
        }
    }

    test ldrhimmT1 {}

    fn strhimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                imm5: u5,
                _: u21,
            }, @bitCast(self.decoder.current));
            self.writeMemU(u16, self.getReg(a.rn) + (@as(u32, a.imm5) << 1), @truncate(self.getReg(a.rt)));
        }
    }

    test strhimmT1 {}

    fn ldrbimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                imm: u5,
                _1: u21,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rt, self.readMemU(u8, self.getReg(a.rn) + a.imm));
        }
    }

    test ldrbimmT1 {}

    fn strbimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                imm: u5,
                _1: u21,
            }, @bitCast(self.decoder.current));
            self.writeMemU(u8, self.getReg(a.rn) + a.imm, @truncate(self.getReg(a.rt)));
        }
    }

    test strbimmT1 {}

    fn ldrimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                imm5: u5,
                _1: u21,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + (@as(u32, a.imm5) << 2);
            const data = self.readMemU(u32, addr);
            self.setReg(a.rt, data);
        }
    }

    test "ldrimmT1" {
        //pass
    }

    fn strimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                t: u3,
                n: u3,
                imm: u5,
                _1: u21,
            }, @bitCast(self.decoder.current));
            self.writeMemU(u32, self.getReg(a.n) + (@as(u32, a.imm) << 2), self.getReg(a.t));
        }
    }

    test strimmT1 {}

    fn ldrregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                t: u3,
                n: u3,
                m: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.n) + self.getReg(a.m);
            const data = self.readMemU(u32, addr);
            self.setReg(a.t, data);
        }
    }

    test ldrregT1 {
        //pass
    }

    fn ldrhregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                rm: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rt, self.readMemU(u16, self.getReg(a.rn) + self.getReg(a.rm)));
        }
    }

    test ldrhregT1 {}

    fn ldrbregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                rm: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));

            self.setReg(a.rt, self.readMemU(u8, self.getReg(a.rn) + self.getReg(a.rm)));
        }
    }

    test ldrbregT1 {}

    fn ldrshregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                rm: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rt, @bitCast(@as(i32, @intCast(@as(i16, @bitCast(self.readMemU(u16, self.getReg(a.rn) + self.getReg(a.rm))))))));
        }
    }

    test ldrshregT1 {}

    fn ldrsbregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                rm: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rt, @bitCast(@as(i32, @intCast(@as(i8, @bitCast(self.readMemU(u8, self.getReg(a.rn) + self.getReg(a.rm))))))));
        }
    }

    test ldrsbregT1 {}

    fn strbregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                t: u3,
                n: u3,
                m: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));
            self.writeMemU(u8, self.getReg(a.n) + self.getReg(a.m), @truncate(self.getReg(a.t)));
        }
    }

    test strbregT1 {}

    fn strhregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                rm: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));
            self.writeMemU(u16, self.getReg(a.rn) + self.getReg(a.rm), @truncate(self.getReg(a.rt)));
        }
    }

    test strhregT1 {}

    fn strregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rt: u3,
                rn: u3,
                rm: u3,
                _1: u23,
            }, @bitCast(self.decoder.current));
            self.writeMemU(u32, self.getReg(a.rn) + self.getReg(a.rm), self.getReg(a.rt));
        }
    }

    test strregT1 {}

    fn popT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            var a: u8 = @truncate(self.decoder.current);
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
            self.setReg(SP_REG, addr);
        }
    }

    test "popT1" {}

    fn revshT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            var r = self.getReg(a.rm);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..2]);
            self.setReg(a.rd, @bitCast(@as(i32, @as(i16, @bitCast(@as(u16, @truncate(r)))))));
        }
    }

    test "revshT1" {}

    fn rev16T1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            var r = self.getReg(a.rm);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..2]);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[2..4]);
            self.setReg(a.rd, r);
        }
    }

    test "rev16T1" {}

    fn revT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                d: u3,
                m: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            var r = self.getReg(a.m);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..4]);
            self.setReg(a.d, r);
        }
    }

    test "revT1" {}

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
            self.setReg(SP_REG, sp);
        }
    }

    test "pushT1" {}

    fn uxtbT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rd, //
                @as(u32, //
                @intCast( //
                    @as(u8, //
                        @truncate( //
                            self.getReg(a.rm))))));
        }
    }

    test uxtbT1 {}

    fn uxthT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rd, //
                @as(u32, //
                @intCast( //
                    @as(u16, //
                        @truncate( //
                            self.getReg(a.rm))))));
        }
    }

    test "uxthT1" {}

    fn sxtbT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u3,
                rm: u3,
                _1: u26,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rd, //
                @bitCast( //
                @as(i32, //
                    @intCast( //
                        @as(i8, //
                            @bitCast( //
                                @as(u8, //
                                    @truncate( //
                                        self.getReg(a.rm)))))))));
        }
    }

    test "sxtbT1" {}

    fn sxthT1(self: *Cpu) void {
        const a = @as(packed struct(u32) { //
            rd: u3,
            rm: u3,
            _1: u26,
        }, @bitCast(self.decoder.current));
        if (self.conditionPassed()) {
            self.setReg(a.rd, //
                @bitCast( //
                @as(i32, //
                    @intCast( //
                        @as(i16, //
                            @bitCast( //
                                @as(u16, //
                                    @truncate( //
                                        self.getReg(a.rm)))))))));
        }
    }

    test sxthT1 {}

    fn itinstr(self: *Cpu) void {
        if (@as(u4, @truncate(self.decoder.current)) == 0) {
            //TODO
            unreachable;
        }
        self.psr.setIT(@truncate(self.decoder.current));
    }

    fn cps(self: *Cpu) void {
        if (self.currentModeIsPrivileged()) {
            const a = @as(packed struct(u32) { //
                affectfault: bool,
                affectpri: bool,
                _1: bool,
                _2: bool,
                disable: bool,
                _3: u27,
            }, @bitCast(self.decoder.current));
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
        const a = @as(packed struct(u32) { //
            imm: i11,
            r: u21,
        }, @bitCast(self.decoder.current));
        const imm32: i32 = (@as(i32, a.imm << 1));
        self.branchWritePC(@as(u32, @bitCast(imm32)) + self.getPC());
    }

    test "bt2" {
        try cpu.init(mem_buf[0..]);
        cpu.PC = 0;
        cpu.setAndExecCurrentInstr(.bT2, 0b10_0000_0000);
        try testing.expect(cpu.PC == (4 + (0xffff_fc00)));
    }

    fn cbzcbnz(self: *Cpu) void {
        const a = @as(packed struct(u16) { //
            rn: u3,
            imm: u5,
            _1: u1,
            i: u1,
            _2: bool,
            op: bool,
            _3: u4,
        }, @bitCast(@as(u16, @truncate(self.decoder.current))));
        const imm3: u32 = (@as(u32, a.i) << 6) | (@as(u32, a.imm) << 1);
        const nonzero = a.op;
        const iszeroRn = self.getReg(a.rn) == 0;
        if ((nonzero or iszeroRn) and (nonzero != iszeroRn)) {
            self.branchWritePC(self.getPC() + imm3);
        }
    }

    test "cbzcbnz" {}

    //===
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

    test "andimmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
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
        });
        cpu.psr.z = false;
        a.imm8 = 0x0;
        cpu.setAndExecCurrentInstr(.andimmT1, @bitCast(a));
        try testing.expect(!cpu.psr.z);

        a.s = true;

        cpu.setAndExecCurrentInstr(.andimmT1, @bitCast(a));
        try testing.expect(cpu.psr.z);

        a.i = 0;
        a.imm3 = 0b011;
        a.imm8 = 0xff;

        a.rd = 1;
        cpu.setReg(a.rd, 0xffff);

        cpu.setAndExecCurrentInstr(.andimmT1, @bitCast(a));
        try testing.expect(cpu.psr.z);

        try testing.expect(cpu.getReg(a.rd) == 0);

        cpu.setReg(a.rn, 0xffff_ffff);

        cpu.setAndExecCurrentInstr(.andimmT1, @bitCast(a));
        try testing.expect(!cpu.psr.z);
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ffff);
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

    test "tstimmT1" {}

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

    test "bicimmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
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
        });

        a.s = false;
        cpu.setAndExecCurrentInstr(.bicimmT1, @bitCast(a));
        try testing.expect(!cpu.psr.z);
        a.s = true;
        cpu.setAndExecCurrentInstr(.bicimmT1, @bitCast(a));
        try testing.expect(cpu.psr.z);

        cpu.setReg(a.rn, 0xffff_ffff);
        a.i = 0;
        a.imm3 = 0;
        a.imm8 = 0xff;

        cpu.setAndExecCurrentInstr(.bicimmT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ff00);
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

    test "orrimmT1" {}

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

    test movimmT2 {}

    fn mvnimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                _2: u4,
                s: bool,
                _3: u5,
                i: u1,
                _4: u5,
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

    test mvnimmT1 {}

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

            const exp = thumbExpandImmC((@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8)), self.psr.c);
            const result = self.getReg(a.rn) | ~exp.val;
            self.setReg(a.rd, result);
            if (a.s) {
                self.psr.n = result & 0x8000_0000 != 0;
                self.psr.z = result == 0;
                self.psr.c = exp.carry;
            }
        }
    }

    test "ornimmT1" {}

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

    test teqimmT1 {}

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

    test "eorimmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
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
        });

        a.i = 0;
        a.imm3 = 0b00;
        a.imm8 = 0xff;

        cpu.setAndExecCurrentInstr(.eorimmT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xff);
    }

    fn cmnimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _0: u4,
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

    test "cmnimmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm8: u8,
            _0: u4,
            imm3: u3,
            _1: u1,
            //half 2
            rn: u4,
            s: bool,
            _2: u5,
            i: u1,
            _3: u5,
        });
        a._0 = 0;
        cpu.psr.z = false;
        cpu.setAndExecCurrentInstr(.cmnimmT1, @bitCast(a));
        try testing.expect(cpu.psr.z);
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

    test "addimmT3" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
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
        });

        cpu.setAndExecCurrentInstr(.addimmT3, @bitCast(a));
        try testing.expect(!cpu.psr.z);

        a.s = true;
        cpu.setAndExecCurrentInstr(.addimmT3, @bitCast(a));
        try testing.expect(cpu.psr.z);

        a.imm8 = 0xff;
        cpu.setAndExecCurrentInstr(.addimmT3, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xff);

        cpu.setReg(a.rn, 0xff);
        cpu.setAndExecCurrentInstr(.addimmT3, @bitCast(a));
        try testing.expect(cpu.getReg(a.rn) == (0xff + 0xff));
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
                self.psr.n = ((result.v & 0x8000_0000) != 0);
                self.psr.z = result.v == 0;
                self.psr.c = result.carry_out;
                self.psr.v = result.overflow;
            }
        }
    }

    test "adcimmT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
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
        });

        a.imm8 = 0;
        cpu.psr.c = true;
        cpu.setAndExecCurrentInstr(.adcimmT1, @bitCast(a));
        try testing.expect(cpu.psr.c);
        try testing.expect(cpu.getReg(0) == 1);
        a.s = true;
        const x: u32 = @bitCast(@as(i32, std.math.maxInt(i32)));
        cpu.setReg(0, x);
        cpu.setAndExecCurrentInstr(.adcimmT1, @bitCast(a));
        try testing.expect(!cpu.psr.c);
        try testing.expect(cpu.psr.v);
        try testing.expect(cpu.getReg(0) == x + 1);

        cpu.setReg(0, 0);
        cpu.setAndExecCurrentInstr(.adcimmT1, @bitCast(a));
        try testing.expect(cpu.psr.z);

        cpu.setReg(0, std.math.maxInt(u32));
        a.imm8 = 1;
        a.rd = 1;
        cpu.setAndExecCurrentInstr(.adcimmT1, @bitCast(a));
        try testing.expect(cpu.psr.z);
        try testing.expect(cpu.psr.c);
        try testing.expect(cpu.getReg(1) == 0);

        cpu.setReg(0, 1);
        cpu.setAndExecCurrentInstr(.adcimmT1, @bitCast(a));
        try testing.expect(cpu.getReg(1) == 3);
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

    test "sbcimmT1" {}

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

    test "cmpimmT2" {
        //pass
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

    test subimmT3 {}

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

    test "rsbimmT2" {}

    fn addimmT4(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                _2: u6,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const exp: u32 = (@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8));

            const res = addWithCarry32(self.getReg(a.rn), exp, false);
            self.setReg(a.rd, res.v);
        }
    }

    test "addimmT4" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm8: u8,
            rd: u4,
            imm3: u3,
            _1: u1,
            //half 2
            rn: u4,
            _2: u6,
            i: u1,
            _3: u5,
        });

        a.i = 1;
        a.imm3 = 0b111;
        a.imm8 = 0xff;

        cpu.setAndExecCurrentInstr(.addimmT4, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0b1111_1111_1111);

        cpu.setReg(a.rd, 0);

        a.i = 0;
        a.imm3 = 0b011;
        a.imm8 = 0xff;

        cpu.setAndExecCurrentInstr(.addimmT4, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0b11_1111_1111);
    }

    fn adrT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                _2: u10,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const imm32: u32 = (@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8));

            self.setReg(a.rd, std.mem.alignBackward(u32, self.getPC(), 4) - imm32);
        }
    }

    test "adrT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm8: u8,
            rd: u4,
            imm3: u3,
            _1: u1,
            //half 2
            _2: u10,
            i: u1,
            _3: u5,
        });

        a.i = 1;
        a.imm3 = 0b111;
        a.imm8 = 0xff;

        cpu.PC = 0;

        cpu.setAndExecCurrentInstr(.adrT2, @bitCast(a));
        var b: u32 = 4;
        b = 4;
        try testing.expect(cpu.getReg(a.rd) == (b - (0xfff)));
    }

    fn adrT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                rn: u4,
                _2: u6,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const imm32: u32 = (@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8));

            self.setReg(a.rd, @addWithOverflow(std.mem.alignBackward(u32, self.getPC(), 4), imm32)[0]);
        }
    }

    test "adrT3" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm8: u8,
            rd: u4,
            imm3: u3,
            _1: u1,
            //half 2
            _2: u10,
            i: u1,
            _3: u5,
        });

        a.i = 1;
        a.imm3 = 0b111;
        a.imm8 = 0xff;

        cpu.PC = 0;

        cpu.setAndExecCurrentInstr(.adrT3, @bitCast(a));
        var b: u32 = 4;
        b = 4;
        try testing.expect(cpu.getReg(a.rd) == (b + (0xfff)));
    }

    fn movimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                imm4: u4,
                _2: u6,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const exp =
                (@as(u16, a.imm4) << 12) |
                (@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8));

            self.setReg(a.rd, exp);
        }
    }

    test movimmT3 {}

    fn subimmT4(self: *Cpu) void {
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

            const exp: u32 = (@as(u12, a.i) << 11) | (@as(u12, a.imm3) << 8) | (@as(u12, a.imm8));
            const result = addWithCarry32(self.getReg(a.rn), ~exp, true);
            self.setReg(a.rd, result.v);
        }
    }

    test subimmT4 {}

    fn movtT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                imm3: u3,
                _1: u1,
                //half 2
                imm4: u4,
                s: bool,
                _2: u5,
                i: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const imm16 = (@as(u16, a.imm4) << 12) | (@as(u16, a.i) << 11) | (@as(u16, a.imm3) << 8) | (@as(u16, a.imm8));
            const res = self.getReg(a.rd) & 0xffff;
            self.setReg(a.rd, res | (@as(u32, imm16) << 16));
        }
    }

    test movtT1 {}

    fn ssatT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                sat_imm: u5,
                _1: u1,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _2: u1,
                //====
                rn: u4,
                _3: u1,
                sh: u1,
                _4: u10,
            }, @bitCast(self.decoder.current));

            const imm3_2 = (@as(u5, a.imm3) << 2) | a.imm2;

            const saturate_to = @as(u32, a.sat_imm) + 1;
            const shft = decodeImmShift(@as(u2, a.sh) << 1, imm3_2);

            const op = shift32(self.getReg(a.rn), shft.t, @truncate(shft.n), self.psr.c);

            const res = signedSatQ(@bitCast(op), saturate_to);

            self.setReg(a.rd, @bitCast(res.result));

            if (res.saturated) {
                self.psr.q = true;
            }
        }
    }

    test ssatT1 {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            sat_imm: u5,
            _1: u1,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _2: u1,
            //====
            rn: u4,
            _3: u1,
            sh: u1,
            _4: u10,
        });

        a.sat_imm = 7;
        cpu.setReg(a.rn, 150);
        cpu.setAndExecCurrentInstr(.ssatT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 127);
        try testing.expect(cpu.psr.q);
    }

    fn @"undefined"(self: *Cpu) void {
        _ = self;
        std.debug.print("undefined. EXITING...\n", .{});
        std.process.exit(0);
        //unreachable;
    }

    fn sbfxT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                widthm1: u5,
                _1: u1,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _2: u1,
                //====
                rn: u4,
                _3: u1,
                sh: u1,
                _4: u10,
            }, @bitCast(self.decoder.current));

            const lsbit = (@as(u5, a.imm3) << 2) | a.imm2;

            const msbit: u6 = lsbit + a.widthm1;

            if (msbit <= 31) {
                self.setReg(a.rd, signExtend(self.getReg(a.rn) >> lsbit, msbit + 1));
            }
        }
    }

    test "sbfxT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            widthm1: u5,
            _1: u1,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _2: u1,
            //====
            rn: u4,
            _3: u1,
            sh: u1,
            _4: u10,
        });

        a.rd = 1;

        cpu.setReg(a.rn, 1);
        cpu.setAndExecCurrentInstr(.sbfxT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ffff);

        a.widthm1 = 31;

        cpu.setReg(a.rn, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.sbfxT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ffff);
    }

    fn bfiT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                msb: u5,
                _1: u1,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _2: u1,
                //====
                rn: u4,
                _3: u12,
            }, @bitCast(self.decoder.current));

            const lsbit: u6 = (@as(u5, a.imm3) << 2) | a.imm2;

            const msbit: u6 = a.msb;

            if (msbit >= lsbit) {
                const res = copyBits(self.getReg(a.rd), lsbit, self.getReg(a.rn), 0, (msbit - lsbit) + 1);
                self.setReg(a.rd, res);
            }
        }
    }

    test "bfiT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            msb: u5,
            _1: u1,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _2: u1,
            //====
            rn: u4,
            _3: u12,
        });

        a.msb = 3;
        a.rd = 1;

        cpu.setReg(a.rn, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfiT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xf);

        a.msb = 31;
        a.rd = 1;

        cpu.setReg(a.rn, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfiT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ffff);

        a.msb = 7;
        a.imm3 = 1;
        a.rd = 1;

        cpu.setReg(a.rn, 0xffff_ffff);
        cpu.setReg(a.rd, 0xdddd_dddd);
        cpu.setAndExecCurrentInstr(.bfiT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xdddd_ddfd);
    }

    fn bfcT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                msb: u5,
                _1: u1,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _2: u1,
                //====
                rn: u4,
                _3: u1,
                sh: u1,
                _4: u10,
            }, @bitCast(self.decoder.current));

            const lsbit: u6 = (@as(u5, a.imm3) << 2) | a.imm2;

            const msbit: u6 = a.msb;

            if (msbit >= lsbit) {
                const res = copyBits(self.getReg(a.rd), lsbit, 0, 0, (msbit - lsbit) + 1);
                self.setReg(a.rd, res);
            }
        }
    }

    test "bfcT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            msb: u5,
            _1: u1,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _2: u1,
            //====
            rn: u4,
            _3: u1,
            sh: u1,
            _4: u10,
        });

        a.msb = 3;
        a.imm2 = 2;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_fff3);

        a.msb = 3;
        a.imm2 = 0;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_fff0);

        a.msb = 7;
        a.imm2 = 0;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ff00);

        a.msb = 15;
        a.imm2 = 0;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_0000);

        a.msb = 23;
        a.imm2 = 0;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xff00_0000);

        a.msb = 27;
        a.imm2 = 0;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xf000_0000);

        a.msb = 30;
        a.imm2 = 0;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0x8000_0000);

        a.msb = 31;
        a.imm2 = 0;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0x0000_0000);

        a.msb = 0;
        a.imm2 = 0;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_fffe);

        a.msb = 7;
        a.imm2 = 0;
        a.imm3 = 1;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ff0f);

        a.msb = 31;
        a.imm2 = 0b11;
        a.imm3 = 0b111;

        cpu.setReg(a.rd, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bfcT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0x7fff_ffff);
    }

    fn usatT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                sat_imm: u5,
                _1: u1,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _2: u1,
                //====
                rn: u4,
                _3: u1,
                sh: u1,
                _4: u10,
            }, @bitCast(self.decoder.current));

            const imm3_2 = (@as(u5, a.imm3) << 2) | a.imm2;

            const saturate_to = @as(u32, a.sat_imm);
            const shft = decodeImmShift(@as(u2, a.sh) << 1, imm3_2);

            const op = shift32(self.getReg(a.rn), shft.t, @truncate(shft.n), self.psr.c);

            const res = unsignedSatQ(@bitCast(op), saturate_to);

            self.setReg(a.rd, @bitCast(res.result));

            if (res.saturated) {
                self.psr.q = true;
            }
        }
    }

    test usatT1 {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            sat_imm: u5,
            _1: u1,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _2: u1,
            //====
            rn: u4,
            _3: u1,
            sh: u1,
            _4: u10,
        });

        cpu.setReg(a.rn, 1000);
        a.sat_imm = 8;
        cpu.setAndExecCurrentInstr(.usatT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 255);
    }

    fn ubfxT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                widthm1: u5,
                _1: u1,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _2: u1,
                //====
                rn: u4,
                _3: u1,
                sh: u1,
                _4: u10,
            }, @bitCast(self.decoder.current));

            const lsbit = (@as(u5, a.imm3) << 2) | a.imm2;

            const msbit: u6 = lsbit + a.widthm1;

            if (msbit <= 31) {
                self.setReg(a.rd, extractBits(self.getReg(a.rn), msbit, lsbit));
            }
        }
    }

    test ubfxT1 {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            widthm1: u5,
            _1: u1,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _2: u1,
            //====
            rn: u4,
            _3: u1,
            sh: u1,
            _4: u10,
        });

        a.rd = 1;
        cpu.setReg(a.rn, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.ubfxT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0x1);

        a.widthm1 = 31;
        cpu.setReg(a.rn, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.ubfxT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ffff);

        a.widthm1 = 0;
        a.imm2 = 0b11;
        a.imm3 = 0b111;
        cpu.setReg(a.rn, 0x8000_0000);
        cpu.setAndExecCurrentInstr(.ubfxT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 1);
    }

    fn bT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm11: u11,
                j2: u1,
                _1: u1,
                j1: u1,
                _2: u2,
                //====
                imm6: u6,
                cond: u4,
                s: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const imm32: i21 = @bitCast((@as(u21, (@as(u3, a.s) << 2) | (@as(u3, a.j2) << 1) | @as(u3, a.j1)) << 18) | (@as(u21, a.imm6) << 12) | (@as(u21, a.imm11) << 1));
            self.branchWritePC(self.getPC() + @as(u32, @bitCast(@as(i32, imm32))));
        }
    }

    test "bT3" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm11: u11,
            j2: u1,
            _1: u1,
            j1: u1,
            _2: u2,
            //====
            imm6: u6,
            cond: u4,
            s: u1,
            _3: u5,
        });

        a.s = 1;
        a.j1 = 1;
        a.j2 = 1;
        a.imm6 = 0b11_1111;
        a.imm11 = 0b111_1111_1111;

        cpu.psr.z = false;

        cpu.decoder.on32 = true;
        cpu.PC = 0;

        cpu.setAndExecCurrentInstr(.bT3, @bitCast(a));

        try testing.expect(cpu.PC == 4);

        cpu.psr.z = true;
        cpu.PC = 0;
        cpu.decoder.on32 = true;

        cpu.setAndExecCurrentInstr(.bT3, @bitCast(a));
        var b: u32 = 0;
        b = 0xffff_fffe;
        try testing.expect(cpu.PC == (b + 4));

        a.s = 1;
        a.j1 = 0;
        a.j2 = 0;
        a.imm6 = 0b11_1111;
        a.imm11 = 0b111_1111_1111;

        cpu.PC = 0;
        cpu.decoder.on32 = true;

        cpu.setAndExecCurrentInstr(.bT3, @bitCast(a));
        b = 0b1111_1111_1111_0011_1111_1111_1111_1110;
        try testing.expect(cpu.PC == (b + 4));
    }

    fn bT4(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm11: u11,
                j2: u1,
                _1: u1,
                j1: u1,
                _2: u2,
                //====
                imm10: u10,
                s: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const i1_ = ~(a.j1 ^ a.s);
            const i2_ = ~(a.j2 ^ a.s);

            const imm32: i25 = @bitCast((@as(u25, (@as(u3, a.s) << 2) | (@as(u3, i1_) << 1) | @as(u3, i2_)) << 22) | (@as(u25, a.imm10) << 12) | (@as(u25, a.imm11) << 1));
            self.branchWritePC(self.getPC() + @as(u32, @bitCast(@as(i32, imm32))));
        }
    }

    test "bT4" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm11: u11,
            j2: u1,
            _1: u1,
            j1: u1,
            _2: u2,
            //====
            imm10: u10,
            s: u1,
            _3: u5,
        });

        a.imm10 = 0x3ff;
        a.imm11 = 0x7ff;

        a.j1 = 1;
        a.j2 = 1;

        a.s = 1;

        cpu.PC = 0;

        cpu.setAndExecCurrentInstr(.bT4, @bitCast(a));
        var b: u32 = 0;
        b = 0xffff_fffe;
        try testing.expect(cpu.PC == (b + 4));

        a.j1 = 0;
        a.j2 = 0;

        a.s = 1;

        cpu.PC = 0;

        cpu.setAndExecCurrentInstr(.bT4, @bitCast(a));
        b = 0b1111_1111_0011_1111_1111_1111_1111_1110;
        try testing.expect(cpu.PC == (b + 4));
    }

    fn msrT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                sysm: u8,
                _1: u8,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const rn = self.getReg(a.rn);

            const sysm = a.sysm;

            switch (sysm >> 3) {
                0 => {
                    if (sysm & 0b100 == 0) {
                        var psr: u32 = @bitCast(self.psr);
                        psr &= 0x7ff_ffff;
                        psr |= (rn & 0xf800_0000);
                        self.psr = @bitCast(psr);
                    }
                },
                1 => {
                    if (self.currentModeIsPrivileged()) {
                        switch (sysm & 0b111) {
                            0 => {
                                self.setReg(SP_MAIN, rn);
                            },
                            1 => {
                                self.setReg(SP_PROC, rn);
                            },
                            else => unreachable,
                        }
                    }
                },
                2 => {
                    switch (sysm & 0b111) {
                        0 => {
                            if (self.currentModeIsPrivileged()) {
                                var primask = @as(u32, @bitCast(self.primask)) & 0xffff_fffe;
                                primask |= (rn & 1);
                                self.primask = @bitCast(primask);
                            }
                        },
                        1 => {
                            if (self.currentModeIsPrivileged()) {
                                var basepri: u32 = @as(u32, @bitCast(self.basepri)) & 0xffff_ff00;
                                basepri |= (rn & 0xff);
                                self.basepri = @bitCast(basepri);
                            }
                        },
                        2 => {
                            if (self.currentModeIsPrivileged() and //
                                (rn & 0xff) != 0 and //
                                ((rn & 0xff < ((@as(u32, @bitCast(self.basepri))) & 0xff)) or //
                                    (((@as(u32, @bitCast(self.basepri))) & 0xff) == 0)))
                            {
                                var basepri: u32 = @as(u32, @bitCast(self.basepri)) & 0xffff_ff00;
                                basepri |= (rn & 0xff);
                                self.basepri = @bitCast(basepri);
                            }
                        },
                        3 => {
                            if (self.currentModeIsPrivileged() and (self.getExecutionPriority() > -1)) {
                                var faultmask = @as(u32, @bitCast(self.faultmask)) & 0xffff_fffe;
                                faultmask |= (rn & 1);
                                self.faultmask = @bitCast(faultmask);
                            }
                        },
                        4 => {
                            if (self.currentModeIsPrivileged()) {
                                var control = @as(u32, @bitCast(self.control));

                                if (self.getMode() == .thread) {
                                    control &= 0xffff_fffc;
                                    control |= (rn & 0b11);
                                } else {
                                    control &= 0xffff_fffe;
                                    control |= (rn & 1);
                                }

                                self.faultmask = @bitCast(control);
                            }
                        },
                        else => unreachable,
                    }
                },
                else => unreachable,
            }
        }
    }

    test "msrT1" {}

    fn mrsT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                sysm: u8,
                rd: u4,
                _1: u4,
                //====
                _2: u16,
            }, @bitCast(self.decoder.current));

            var rd: u32 = 0;

            const sysm = a.sysm;

            const psr = @as(u32, @bitCast(self.psr));

            switch (sysm >> 3) {
                0b0 => {
                    if ((sysm & 1) == 1 and self.currentModeIsPrivileged()) {
                        rd |= (psr & 0x1ff);
                    }

                    if ((sysm & 0b10) == 0b10) {
                        rd &= 0b1111_1000_1111_1111_1111_1111_1111_1111;
                        rd &= 0b1111_1111_1111_1111_1000_0001_1111_1111;
                    }

                    if ((sysm & 0b100) == 0b0) {
                        rd |= (psr & 0b1111_1000_0000_0000_0000_0000_0000_0000);
                    }
                },
                0b1 => {
                    if (self.currentModeIsPrivileged()) {
                        switch (sysm & 0b111) {
                            0 => {
                                rd = self.getReg(SP_MAIN);
                            },
                            1 => {
                                rd = self.getReg(SP_PROC);
                            },
                            else => unreachable,
                        }
                    }
                },
                0b10 => {
                    switch (sysm & 0b111) {
                        0 => {
                            rd &= 0xffff_fffe;
                            if (self.currentModeIsPrivileged()) {
                                rd |= (@as(u32, @bitCast(self.primask)) & 1);
                            }
                        },
                        1, 2 => {
                            rd &= 0xffff_ff00;
                            if (self.currentModeIsPrivileged()) {
                                rd |= (@as(u32, @bitCast(self.basepri)) & 0xff);
                            }
                        },
                        3 => {
                            rd &= 0xffff_fffe;
                            if (self.currentModeIsPrivileged()) {
                                rd |= (@as(u32, @bitCast(self.faultmask)) & 1);
                            }
                        },
                        4 => {
                            rd &= 0xffff_fffc;
                            rd |= (@as(u32, @bitCast(self.control)) & 0b11);
                        },
                        else => unreachable,
                    }
                },
                else => unreachable,
            }

            self.setReg(a.rd, rd);
        }
    }

    test "mrsT1" {}

    fn blT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm11: u11,
                j2: u1,
                _1: u1,
                j1: u1,
                _2: u2,
                //====
                imm10: u10,
                s: u1,
                _3: u5,
            }, @bitCast(self.decoder.current));

            const i1_ = ~(a.j1 ^ a.s);
            const i2_ = ~(a.j2 ^ a.s);

            const imm32: i25 = @bitCast((@as(u25, (@as(u3, a.s) << 2) | (@as(u3, i1_) << 1) | @as(u3, i2_)) << 22) | (@as(u25, a.imm10) << 12) | (@as(u25, a.imm11) << 1));

            self.setRL(self.getPC() | 1);
            self.branchWritePC(self.getPC() + @as(u32, @bitCast(@as(i32, imm32))));
        }
    }

    test "blT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            imm11: u11,
            j2: u1,
            _1: u1,
            j1: u1,
            _2: u2,
            //====
            imm10: u10,
            s: u1,
            _3: u5,
        });

        const target: u32 = 0b1111_1111_1111_1111_1111_1111_1111_1110;

        a.imm11 = 0x7ff;
        a.s = 1;
        a.j1 = 1;
        a.j2 = 1;
        a.imm10 = 0x3ff;

        const pc = cpu.getPC();
        cpu.setAndExecCurrentInstr(.blT1, @bitCast(a));
        try testing.expect(cpu.PC == target + pc);
        try testing.expect(cpu.getRL() == pc | 1);
    }

    fn nop(self: *Cpu) void {
        _ = self;
    }

    fn yield(self: *Cpu) void {
        std.debug.print("=================>>>>>> panic ... yield. exit...\n", .{});
        std.debug.print("memory dump: {x}\n", .{self.memory[0x5ace8..][0..1000]});
        std.process.exit(0);
        //_ = self;
    }

    fn wfe(self: *Cpu) void {
        std.debug.print("wfe FAIL ==============================================================\n", .{});
        _ = self;
    }

    fn wfi(self: *Cpu) void {
        std.debug.print("wfi PASS ==============================================================\n", .{});
        _ = self;
    }

    fn sev(self: *Cpu) void {
        std.debug.print("SEV ==============================================================\n", .{});
        _ = self;
    }

    fn dbg(self: *Cpu) void {
        _ = self;
    }

    fn clrex(self: *Cpu) void {
        _ = self;
    }

    fn dsb(self: *Cpu) void {
        _ = self;
    }

    fn dmb(self: *Cpu) void {
        _ = self;
    }

    fn isb(self: *Cpu) void {
        _ = self;
    }

    fn stmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                register_list: u13,
                _1: u1,
                M: bool,
                _2: u1,
                //====
                rn: u4,
                _3: u1,
                W: bool,
                _4: u10,
            }, @bitCast(self.decoder.current));

            var registers: u16 = a.register_list;
            if (a.M) registers |= (1 << 14);

            //var bc:usize = 0;
            const n = a.rn;

            var address = self.getReg(n);

            for (0..15) |i| {
                if (registers & 1 > 0) {
                    self.writeMemA(u32, address, self.getReg(i));
                    address = @addWithOverflow(address, 4)[0];
                    //bc+=1;
                }
                registers >>= 1;
            }

            if (a.W) {
                self.setReg(n, address);
            }
        }
    }

    fn ldmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                register_list: u13,
                _1: u1,
                M: bool,
                P: bool,
                //====
                rn: u4,
                _3: u1,
                W: bool,
                _4: u10,
            }, @bitCast(self.decoder.current));

            var registers: u16 = a.register_list;
            if (a.M) registers |= (1 << 14);
            if (a.P) registers |= (1 << 15);

            //var bc:usize = 0;
            const n = a.rn;

            var address = self.getReg(n);
            var wb = false;
            for (0..15) |i| {
                if (registers & 1 > 0) {
                    self.setReg(i, self.readMemA(u32, address));
                    address += 4;
                    //bc+=1;
                } else {
                    if (i == n) {
                        wb = true;
                    }
                }
                registers >>= 1;
            }

            if (registers & 1 > 0) {
                self.loadWritePC(self.readMemA(u32, address));
                address = @addWithOverflow(address, 4)[0];
            } else {
                if (n == 15) {
                    wb = true;
                }
            }

            if (a.W and wb) {
                self.setReg(n, address);
            }
        }
    }

    test "ldmT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            register_list: u13,
            _1: u1,
            M: bool,
            P: bool,
            //====
            rn: u4,
            _3: u1,
            W: bool,
            _4: u10,
        });
        a.P = true;
        a.M = true;
        a.rn = 13;
        a.W = true;
        try cpu.mem_steam.seekTo(0);
        for (0..16) |i| {
            try cpu.mem_steam.writer().writeInt(u32, @truncate(i), .big);
        }

        a.register_list = 0x1fff;
        cpu.setReg(a.rn, 0);
        cpu.setAndExecCurrentInstr(.ldmT2, @bitCast(a));

        for (0..a.rn) |i| {
            try testing.expect(cpu.getReg(i) == i);
        }

        try testing.expect(cpu.getReg(a.rn) == (15 * 4));
        try testing.expect(cpu.PC == 14);
    }

    fn popT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                register_list: u13,
                _1: u1,
                M: bool,
                P: bool,
                //====
                _2: u16,
            }, @bitCast(self.decoder.current));

            var registers: u16 = a.register_list;
            if (a.M) registers |= (1 << 14);
            if (a.P) registers |= (1 << 15);

            var address = self.getReg(SP_REG);

            for (0..15) |i| {
                if (registers & 1 > 0) {
                    self.setReg(i, self.readMemA(u32, address));
                    address += 4;
                    //bc+=1;
                }
                registers >>= 1;
            }

            if (registers & 1 > 0) {
                self.loadWritePC(self.readMemA(u32, address));
                address += 4;
            }

            self.setReg(SP_REG, address);
        }
    }

    test "popT2" {}

    fn popT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                _1: u12,
                rt: u4,
                //====
                _2: u16,
            }, @bitCast(self.decoder.current));

            const address = self.getReg(SP_REG);

            if (a.rt == 15) {
                self.loadWritePC(self.readMemA(u32, address));
            } else {
                self.setReg(a.rt, self.readMemA(u32, address));
            }

            self.setReg(SP_REG, address + 4);
        }
    }

    test "popT3" {}

    fn stmdbT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                register_list: u13,
                _1: u1,
                M: bool,
                _2: bool,
                //====
                rn: u4,
                _3: u1,
                W: bool,
                _4: u10,
            }, @bitCast(self.decoder.current));

            var registers: u16 = a.register_list;
            if (a.M) registers |= (1 << 14);

            var address = self.getReg(a.rn) - (4 * bitCount(u16, registers));
            const add = address;

            for (0..15) |i| {
                if (registers & 1 > 0) {
                    self.writeMemA(u32, address, self.getReg(i));
                    address += 4;
                }
                registers >>= 1;
            }

            if (a.W) {
                self.setReg(a.rn, add);
            }
        }
    }

    test stmdbT1 {}

    fn pushT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                register_list: u13,
                _1: u1,
                M: bool,
                P: bool,
                //====
                _2: u16,
            }, @bitCast(self.decoder.current));

            var registers: u16 = a.register_list;
            if (a.M) registers |= (1 << 14);

            var address = self.getReg(SP_REG) - (4 * bitCount(u16, registers));
            const add = address;

            for (0..15) |i| {
                if (registers & 1 > 0) {
                    self.writeMemA(u32, address, self.getReg(i));
                    address += 4;
                    //bc+=1;
                }
                registers >>= 1;
            }

            self.setReg(SP_REG, add);
        }
    }

    test "pushT2" {}

    fn pushT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                _1: u12,
                rt: u4,
                //====
                _2: u16,
            }, @bitCast(self.decoder.current));

            const address = self.getReg(SP_REG) - 4;
            self.writeMemA(u32, address, self.getReg(a.rt));
            self.setReg(SP_REG, address);
        }
    }

    test "pushT3" {}

    fn ldmdbT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                register_list: u13,
                _1: u1,
                M: bool,
                P: bool,
                //====
                rn: u4,
                _3: u1,
                W: bool,
                _4: u10,
            }, @bitCast(self.decoder.current));

            var registers: u16 = a.register_list;
            if (a.M) registers |= (1 << 14);
            if (a.P) registers |= (1 << 15);

            const n = a.rn;

            var address = self.getReg(n) - (4 * bitCount(u16, registers));
            const add = address;

            var wb = false;
            for (0..15) |i| {
                if (registers & 1 > 0) {
                    self.setReg(i, self.readMemA(u32, address));
                    address += 4;
                    //bc+=1;
                } else {
                    if (i == n) {
                        wb = true;
                    }
                }
                registers >>= 1;
            }

            if (registers & 1 > 0) {
                self.loadWritePC(self.readMemA(u32, address));
            } else {
                if (n == 15) {
                    wb = true;
                }
            }

            if (a.W and wb) {
                self.setReg(n, add);
            }
        }
    }

    test "ldmdbT1" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            register_list: u13,
            _1: u1,
            M: bool,
            P: bool,
            //====
            rn: u4,
            _3: u1,
            W: bool,
            _4: u10,
        });
        a.P = true;
        a.M = true;
        a.rn = 13;
        a.W = true;
        try cpu.mem_steam.seekTo(0);
        for (0..15) |i| {
            try cpu.mem_steam.writer().writeInt(u32, @truncate(i), .big);
        }

        a.register_list = 0x1fff;
        cpu.setReg(a.rn, (15 * 4));
        cpu.setAndExecCurrentInstr(.ldmdbT1, @bitCast(a));

        for (0..a.rn) |i| {
            try testing.expect(cpu.getReg(i) == i);
        }

        try testing.expect(cpu.getReg(a.rn) == 0);
        try testing.expect(cpu.PC == 14);
    }

    fn strexT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const address = self.getReg(a.rn) + (@as(u32, a.imm8) << 2);

            if (self.exclusiveMonitorsPass(address, 4)) {
                self.writeMemA(u32, address, self.getReg(a.rt));
                self.setReg(a.rd, 0);
            } else {
                self.setReg(a.rd, 1);
            }
        }
    }

    test "strexT1" {}

    fn ldrexT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rd: u4,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));
            const address = self.getReg(a.rn) + (@as(u32, a.imm8) << 2);
            self.setExclusiveMonitors(address, 4);
            self.setReg(a.rt, self.readMemA(u32, address));
        }
    }

    test ldrexT1 {}

    fn strdimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rt2: u4,
                rt: u4,
                //====
                rn: u4,
                _1: u1,
                W: bool,
                _2: u1,
                U: bool,
                P: bool,
                _3: u7,
            }, @bitCast(self.decoder.current));

            const index = a.P;
            const add = a.U;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + (@as(u32, a.imm8) << 2) else //
                self.getReg(a.rn) - (@as(u32, a.imm8) << 2);

            const addr = if (index) offset_addr else self.getReg(a.rn);

            self.writeMemA(u32, addr, self.getReg(a.rt));
            self.writeMemA(u32, addr + 4, self.getReg(a.rt2));

            if (wback) self.setReg(a.rn, offset_addr);
        }
    }

    test strdimmT1 {}

    fn ldrdimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rt2: u4,
                rt: u4,
                //====
                rn: u4,
                _1: u1,
                W: bool,
                _2: u1,
                U: bool,
                P: bool,
                _3: u7,
            }, @bitCast(self.decoder.current));

            const index = a.P;
            const add = a.U;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + (@as(u32, a.imm8) << 2) else //
                self.getReg(a.rn) - (@as(u32, a.imm8) << 2);

            const addr = if (index) offset_addr else self.getReg(a.rn);

            self.setReg(a.rt, self.readMemA(u32, addr));
            self.setReg(a.rt2, self.readMemA(u32, addr + 4));

            if (wback) self.setReg(a.rn, offset_addr);
        }
    }

    test ldrdimmT1 {}

    fn ldrdlitT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                rt2: u4,
                rt: u4,
                //====
                rn: u4,
                _1: u3,
                U: bool,
                P: bool,
                _2: u7,
            }, @bitCast(self.decoder.current));

            const addr = if (a.U) self.getReg(a.rn) + (@as(u32, a.imm8) << 2) else //
                self.getReg(a.rn) - (@as(u32, a.imm8) << 2);

            self.setReg(a.rt, self.readMemA(u32, addr));
            self.setReg(a.rt2, self.readMemA(u32, addr + 4));
        }
    }

    test ldrdlitT1 {}

    fn strexbT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u4,
                _1: u8,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const address = self.getReg(a.rn);

            if (self.exclusiveMonitorsPass(address, 1)) {
                self.writeMemA(u8, address, @truncate(self.getReg(a.rt)));
                self.setReg(a.rd, 0);
            } else {
                self.setReg(a.rd, 1);
            }
        }
    }

    test "strexbT1" {}

    fn strexhT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rd: u4,
                _1: u8,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const address = self.getReg(a.rn);

            if (self.exclusiveMonitorsPass(address, 2)) {
                self.writeMemA(u16, address, @truncate(self.getReg(a.rt)));
                self.setReg(a.rd, 0);
            } else {
                self.setReg(a.rd, 1);
            }
        }
    }

    test "strexhT1" {}

    fn tbbT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                H: bool,
                _1: u11,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const half_words = if (a.H)
                self.readMemA(u16, self.getReg(a.rn + std.math.shl(u32, self.getReg(a.rm), 1)))
            else
                @as(u16, self.readMemA(u8, self.getReg(a.rn + self.getReg(a.rm))));

            self.branchWritePC(self.getPC() + (2 * half_words));
        }
    }

    test tbbT1 {}

    fn ldrexbT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                _0: u8,
                rd: u4,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));
            const address = self.getReg(a.rn);
            self.setExclusiveMonitors(address, 1);
            self.setReg(a.rt, self.readMemA(u8, address));
        }
    }

    test ldrexbT1 {}

    fn ldrexhT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                _0: u8,
                rd: u4,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));
            const address = self.getReg(a.rn);
            self.setExclusiveMonitors(address, 2);
            self.setReg(a.rt, self.readMemA(u16, address));
        }
    }

    test ldrexhT1 {}

    fn ldrimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const addr = self.getReg(a.rn) + a.imm12;
            const data = self.readMemU(u32, addr);

            if (a.rt == 15) {
                if (addr & 0b11 == 0) {
                    self.loadWritePC(data);
                }
            } else {
                self.setReg(a.rt, data);
            }
        }
    }

    test "ldrimmT3" {
        //pass
    }

    fn ldrimmT4(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                W: bool,
                U: bool,
                P: bool,
                _1: u1,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const add = a.U;
            const index = a.P;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + a.imm8 else self.getReg(a.rn) - a.imm8;
            const addr = if (index) offset_addr else self.getReg(a.rn);
            const data = self.readMemU(u32, addr);
            if (wback) self.setReg(a.rn, offset_addr);
            if (a.rt == 15) {
                if (addr & 0b11 == 0) {
                    self.loadWritePC(data);
                }
            } else {
                self.setReg(a.rt, data);
            }
        }
    }

    test ldrimmT4 {
        //pass
    }

    fn ldrregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                imm2: u2,
                _0: u6,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const offset = shift32(self.getReg(a.rm), .lsl, a.imm2, self.psr.c);
            const address = self.getReg(a.rn) + offset;
            const data = self.readMemU(u32, address);

            if (a.rt == 15) {
                if (address & 0b11 == 0) {
                    self.loadWritePC(data);
                }
            } else {
                self.setReg(a.rt, data);
            }
        }
    }

    test ldrregT2 {}

    fn ldrlitT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                _2: u7,
                U: bool,
                _1: u8,
            }, @bitCast(self.decoder.current));

            const base = std.mem.alignBackward(u32, self.getPC(), 4);
            const address = if (a.U) base + a.imm12 else base - a.imm12;
            const data = self.readMemU(u32, address);

            if (a.rt == 15) {
                if (address & 0b11 == 0) {
                    self.loadWritePC(data);
                }
            } else {
                self.setReg(a.rt, data);
            }
        }
    }

    test ldrlitT2 {
        //pass
    }

    fn ldrhimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm12;
            self.setReg(a.rt, self.readMemU(u16, addr));
        }
    }

    test ldrhimmT2 {}

    fn ldrhimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                W: bool,
                U: bool,
                P: bool,
                _1: u1,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const add = a.U;
            const index = a.P;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + a.imm8 else self.getReg(a.rn) - a.imm8;
            const addr = if (index) offset_addr else self.getReg(a.rn);
            const data = self.readMemU(u16, addr);
            if (wback) self.setReg(a.rn, offset_addr);
            self.setReg(a.rt, data);
        }
    }

    test ldrhimmT3 {}

    fn ldrhtT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _1: u4,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const addr = self.getReg(a.rn) + a.imm8;
            const data = self.readMemU_Unpriv(u16, addr);

            self.setReg(a.rt, data);
        }
    }

    test ldrhtT1 {}

    fn ldrtT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _1: u4,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const addr = self.getReg(a.rn) + a.imm8;
            const data = self.readMemU_Unpriv(u32, addr);

            self.setReg(a.rt, data);
        }
    }

    test ldrtT1 {}

    fn ldrhlitT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                _0: u7,
                U: bool,
                _1: u8,
            }, @bitCast(self.decoder.current));
            const base = std.mem.alignBackward(u32, self.getPC(), 4);
            const addr = if (a.U) base + a.imm12 else base - a.imm12;
            self.setReg(a.rt, self.readMemU(u16, addr));
        }
    }

    fn ldrhregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                imm2: u2,
                _0: u6,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const offset = shift32(self.getReg(a.rm), .lsl, a.imm2, self.psr.c);
            const address = self.getReg(a.rn) + offset;
            const data = self.readMemU(u16, address);
            self.setReg(a.rt, data);
        }
    }

    test ldrhregT2 {}

    fn ldrshimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm12;
            const data = self.readMemU(u16, addr);
            self.setReg(a.rt, @bitCast(@as(i32, @as(i16, @bitCast(data)))));
        }
    }

    test ldrshimmT1 {}

    fn ldrshimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                W: bool,
                U: bool,
                P: bool,
                _1: u1,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const add = a.U;
            const index = a.P;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + a.imm8 else self.getReg(a.rn) - a.imm8;
            const addr = if (index) offset_addr else self.getReg(a.rn);
            const data = self.readMemU(u16, addr);
            if (wback) self.setReg(a.rn, offset_addr);
            self.setReg(a.rt, @bitCast(@as(i32, @as(i16, @bitCast(data)))));
        }
    }

    test ldrshimmT2 {}

    fn ldrshtT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _1: u4,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm8;
            const data = self.readMemU_Unpriv(u16, addr);
            self.setReg(a.rt, @bitCast(@as(i32, @as(i16, @bitCast(data)))));
        }
    }

    test ldrshtT1 {}

    fn ldrshlitT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                _0: u7,
                U: bool,
                _1: u8,
            }, @bitCast(self.decoder.current));

            const base = std.mem.alignBackward(u32, self.getPC(), 4);
            const address = if (a.U) base + a.imm12 else base - a.imm12;
            const data = self.readMemU(u16, address);
            self.setReg(a.rt, @bitCast(@as(i32, @as(i16, @bitCast(data)))));
        }
    }

    test ldrshlitT1 {}
    //TODO optimize shifts
    fn ldrshregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                imm2: u2,
                _0: u6,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const offset = shift32(self.getReg(a.rm), .lsl, a.imm2, self.psr.c);
            const address = self.getReg(a.rn) + offset;
            const data = self.readMemU(u16, address);

            self.setReg(a.rt, @bitCast(@as(i32, @as(i16, @bitCast(data)))));
        }
    }

    test ldrshregT2 {}

    fn ldrbimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm12;
            self.setReg(a.rt, self.readMemU(u8, addr));
        }
    }

    test ldrbimmT2 {}

    fn ldrbimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                W: bool,
                U: bool,
                P: bool,
                _1: u1,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const add = a.U;
            const index = a.P;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + a.imm8 else self.getReg(a.rn) - a.imm8;
            const addr = if (index) offset_addr else self.getReg(a.rn);
            const data = self.readMemU(u8, addr);
            self.setReg(a.rt, data);
            if (wback) self.setReg(a.rn, offset_addr);
        }
    }

    test ldrbimmT3 {}

    fn ldrbtT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _1: u4,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const addr = self.getReg(a.rn) + a.imm8;
            const data = self.readMemU_Unpriv(u8, addr);

            self.setReg(a.rt, data);
        }
    }

    test ldrbtT1 {}

    fn ldrblitT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                _0: u7,
                U: bool,
                _1: u8,
            }, @bitCast(self.decoder.current));
            const base = std.mem.alignBackward(u32, self.getPC(), 4);
            const addr = if (a.U) base + a.imm12 else base - a.imm12;
            self.setReg(a.rt, self.readMemU(u8, addr));
        }
    }

    test ldrblitT1 {}

    fn ldrbregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                imm2: u2,
                rd: u6,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const offset = shift32(self.getReg(a.rm), .lsl, a.imm2, self.psr.c);
            const address = self.getReg(a.rn) + offset;
            const data = self.readMemU(u8, address);
            self.setReg(a.rt, data);
        }
    }

    test ldrbregT2 {}

    fn ldrsbimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm12;
            const data = self.readMemU(u8, addr);
            self.setReg(a.rt, @bitCast(@as(i32, @as(i8, @bitCast(data)))));
        }
    }

    test ldrsbimmT1 {
        try cpu.init(mem_buf[0..]);
        const a = std.mem.zeroes(packed struct(u32) { //
            imm12: u12,
            rt: u4,
            //====
            rn: u4,
            _2: u12,
        });

        cpu.memory[0] = 0xff;
        cpu.setAndExecCurrentInstr(.ldrsbimmT1, @bitCast(a));
        try testing.expect(cpu.getReg(a.rt) == 0xffff_ffff);
    }

    fn ldrsbimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                W: bool,
                U: bool,
                P: bool,
                _1: u1,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const add = a.U;
            const index = a.P;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + a.imm8 else self.getReg(a.rn) - a.imm8;
            const addr = if (index) offset_addr else self.getReg(a.rn);
            const data = self.readMemU(u8, addr);

            self.setReg(a.rt, @bitCast(@as(i32, @as(i8, @bitCast(data)))));
            if (wback) self.setReg(a.rn, offset_addr);
        }
    }

    test ldrsbimmT2 {}

    fn ldrsbtT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _1: u4,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm8;
            const data = self.readMemU_Unpriv(u8, addr);
            self.setReg(a.rt, @bitCast(@as(i32, @as(i8, @bitCast(data)))));
        }
    }

    test ldrsbtT1 {}

    fn ldrsblitT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                _0: u7,
                U: bool,
                _1: u8,
            }, @bitCast(self.decoder.current));

            const base = std.mem.alignBackward(u32, self.getPC(), 4);
            const address = if (a.U) base + a.imm12 else base - a.imm12;
            const data = self.readMemU(u8, address);

            self.setReg(a.rt, @bitCast(@as(i32, @as(i8, @bitCast(data)))));
        }
    }

    test ldrsblitT1 {}

    fn ldrsbregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                imm2: u2,
                _0: u6,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const offset = shift32(self.getReg(a.rm), .lsl, a.imm2, self.psr.c);
            const address = self.getReg(a.rn) + offset;
            const data = self.readMemU(u8, address);

            self.setReg(a.rt, @bitCast(@as(i32, @as(i8, @bitCast(data)))));
        }
    }

    test ldrsbregT2 {}

    fn strbimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm12;
            self.writeMemU(u8, addr, @truncate(self.getReg(a.rt)));
        }
    }

    test "strbimmT2" {}

    fn strbimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                W: bool,
                U: bool,
                P: bool,
                _1: u1,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const add = a.U;
            const index = a.P;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + a.imm8 else self.getReg(a.rn) - a.imm8;
            const addr = if (index) offset_addr else self.getReg(a.rn);
            self.writeMemU(u8, addr, @truncate(self.getReg(a.rt)));
            if (wback) self.setReg(a.rn, offset_addr);
        }
    }

    test "strbimmT3" {}

    fn strbregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                imm2: u2,
                _0: u6,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const offset = shift32(self.getReg(a.rm), .lsl, a.imm2, self.psr.c);
            const address = self.getReg(a.rn) + offset;
            self.writeMemU(u8, address, @truncate(self.getReg(a.rt)));
        }
    }

    test strbregT2 {}

    fn strhimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm12;
            self.writeMemU(u16, addr, @truncate(self.getReg(a.rt)));
        }
    }

    test strhimmT2 {}

    fn strhimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                W: bool,
                U: bool,
                P: bool,
                _1: u1,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const add = a.U;
            const index = a.P;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + a.imm8 else self.getReg(a.rn) - a.imm8;
            const addr = if (index) offset_addr else self.getReg(a.rn);
            self.writeMemU(u16, addr, @truncate(self.getReg(a.rt)));
            if (wback) self.setReg(a.rn, offset_addr);
        }
    }

    test strhimmT3 {}

    fn strhregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                imm2: u2,
                rd: u6,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));

            const offset = shift32(self.getReg(a.rm), .lsl, a.imm2, self.psr.c);
            const address = self.getReg(a.rn) + offset;
            self.writeMemU(u16, address, @truncate(self.getReg(a.rt)));
        }
    }

    test strhregT2 {}

    fn strimmT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm12: u12,
                rt: u4,
                //====
                rn: u4,
                _1: u12,
            }, @bitCast(self.decoder.current));
            const addr = self.getReg(a.rn) + a.imm12;
            self.writeMemU(u32, addr, self.getReg(a.rt));
        }
    }

    test strimmT3 {}

    fn strimmT4(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                W: bool,
                U: bool,
                P: bool,
                _1: u1,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const add = a.U;
            const index = a.P;
            const wback = a.W;

            const offset_addr = if (add) self.getReg(a.rn) + a.imm8 else self.getReg(a.rn) - a.imm8;
            const addr = if (index) offset_addr else self.getReg(a.rn);
            self.writeMemU(u32, addr, self.getReg(a.rt));
            if (wback) self.setReg(a.rn, offset_addr);
        }
    }

    test strimmT4 {}

    fn strregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                imm2: u2,
                _1: u6,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            const offset = shift32(self.getReg(a.rm), .lsl, a.imm2, self.psr.c);
            const address = self.getReg(a.rn) + offset;
            self.writeMemU(u32, address, self.getReg(a.rt));
        }
    }

    test strregT2 {}

    fn andregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = self.getReg(a.rn) & shres.value;
            self.setReg(a.rd, res);
            if (a.S) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
                self.psr.c = shres.carry;
            }
        }
    }

    test "andregT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rm: u4,
            typ: Shift,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _0: u1,
            //====
            rn: u4,
            S: bool,
            _1: u11,
        });

        cpu.psr.z = false;
        cpu.setAndExecCurrentInstr(.andregT2, @bitCast(a));
        try testing.expect(!cpu.psr.z);
        a.S = true;
        cpu.setAndExecCurrentInstr(.andregT2, @bitCast(a));
        try testing.expect(cpu.psr.z);

        a.rm = 1;
        a.rn = 2;
        a.imm2 = 0b11;
        a.imm3 = 0b111;
        a.typ = .lsl;
        a.rd = 3;

        cpu.setReg(a.rm, 0xffff_ffff);
        cpu.setReg(a.rn, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.andregT2, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0x8000_0000);
    }

    fn tstregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = self.getReg(a.rn) & shres.value;

            self.psr.n = res & 0x8000_0000 != 0;
            self.psr.z = res == 0;
            self.psr.c = shres.carry;
        }
    }

    test tstregT2 {}

    fn bicregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = self.getReg(a.rn) & ~shres.value;
            self.setReg(a.rd, res);
            if (a.S) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
                self.psr.c = shres.carry;
            }
        }
    }

    test "bicregT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rm: u4,
            typ: Shift,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _0: u1,
            //====
            rn: u4,
            S: bool,
            _1: u11,
        });

        a.rm = 1;
        a.rd = 2;
        a.imm2 = 1;
        a.typ = .lsl;

        a.S = true;
        cpu.psr.z = true;

        cpu.setReg(a.rm, 0xfff);
        cpu.setReg(a.rn, 0xffff_ffff);
        cpu.setAndExecCurrentInstr(.bicregT2, @bitCast(a));

        try testing.expect(cpu.getReg(a.rd) == (0xffff_ffff & ~@as(u32, 0xfff << 1)));
        try testing.expect(!cpu.psr.z);
    }

    fn orrregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));
            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = self.getReg(a.rn) | shres.value;
            self.setReg(a.rd, res);
            if (a.S) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
                self.psr.c = shres.carry;
            }
        }
    }

    test "orrregT2" {}

    fn ornregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = self.getReg(a.rn) | ~shres.value;
            self.setReg(a.rd, res);
            if (a.S) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
                self.psr.c = shres.carry;
            }
        }
    }

    test "ornregT1" {}

    fn mvnregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                _1: u4,
                S: bool,
                _2: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = ~shres.value;
            self.setReg(a.rd, res);
            if (a.S) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
                self.psr.c = shres.carry;
            }
        }
    }

    test mvnregT2 {}

    fn eorregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = self.getReg(a.rn) ^ shres.value;
            self.setReg(a.rd, res);
            if (a.S) {
                self.psr.n = res & 0x8000_0000 != 0;
                self.psr.z = res == 0;
                self.psr.c = shres.carry;
            }
        }
    }

    test "eorregT2" {
        //pass
    }

    fn teqregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = self.getReg(a.rn) ^ shres.value;

            self.psr.n = res & 0x8000_0000 != 0;
            self.psr.z = res == 0;
            self.psr.c = shres.carry;
        }
    }

    test teqregT1 {}

    fn addregT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = addWithCarry32(self.getReg(a.rn), shres.value, false);

            if (a.rd == 15) {
                self.aluWritePc(res.v);
            } else {
                self.setReg(a.rd, res.v);
                if (a.S) {
                    self.psr.n = res.v & 0x8000_0000 != 0;
                    self.psr.z = res.v == 0;
                    self.psr.c = res.carry_out;
                    self.psr.v = res.overflow;
                }
            }
        }
    }

    test "addregT3" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rm: u4,
            typ: Shift,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _0: u1,
            //====
            rn: u4,
            S: bool,
            _1: u11,
        });

        a.rm = 1;
        a.rd = 3;
        a.rn = 0;
        a.imm2 = 1;
        a.imm3 = 0b100;

        cpu.psr.c = true;

        a.typ = .lsl;
        a.S = true;

        cpu.setReg(a.rm, 30);
        cpu.setReg(a.rn, 40);

        cpu.setAndExecCurrentInstr(.addregT3, @bitCast(a));
        try testing.expect(!cpu.psr.c);
        try testing.expect(cpu.getReg(a.rd) == (40 + (30 << 0b10001)));
    }

    fn cmnregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = addWithCarry32(self.getReg(a.rn), shres.value, false);

            self.psr.n = res.v & 0x8000_0000 != 0;
            self.psr.z = res.v == 0;
            self.psr.c = res.carry_out;
            self.psr.v = res.overflow;
        }
    }

    test "cmnregT2" {
        //pass
    }

    fn adcregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = addWithCarry32(self.getReg(a.rn), shres.value, self.psr.c);

            self.setReg(a.rd, res.v);
            if (a.S) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    test "adcregT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rm: u4,
            typ: Shift,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _0: u1,
            //====
            rn: u4,
            S: bool,
            _1: u11,
        });
        a.S = true;
        cpu.psr.c = true;
        cpu.setAndExecCurrentInstr(.adcregT2, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 1);
        try testing.expect(!cpu.psr.c);

        a.typ = .lsl;
        a.imm2 = 1;
        cpu.setAndExecCurrentInstr(.adcregT2, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 3);

        a.typ = .lsr;
        a.imm2 = 1;
        cpu.setAndExecCurrentInstr(.adcregT2, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 4);

        a.typ = .ror;
        a.imm2 = 1;
        cpu.setReg(a.rm, 1);
        cpu.setAndExecCurrentInstr(.adcregT2, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0x8000_0001);

        try testing.expect(cpu.psr.n);
    }

    fn sbcregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = addWithCarry32(self.getReg(a.rn), ~shres.value, self.psr.c);
            self.setReg(a.rd, res.v);
            if (a.S) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    test sbcregT2 {}

    fn subregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = addWithCarry32(self.getReg(a.rn), ~shres.value, true);
            self.setReg(a.rd, res.v);
            if (a.S) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                self.psr.z = res.v == 0;
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    test subregT2 {}

    fn cmpregT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                _1: u4,
                imm3: u3,
                _2: u1,
                //====
                rn: u4,
                _3: u12,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = addWithCarry32(self.getReg(a.rn), ~shres.value, true);

            self.psr.n = res.v & 0x8000_0000 != 0;
            self.psr.z = res.v == 0;
            self.psr.c = res.carry_out;
            self.psr.v = res.overflow;
        }
    }

    test "cmpregT3" {
        //
    }

    fn rsbregT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const sh = decodeImmShift(a.typ, (@as(u5, a.imm3) << 2) | a.imm2);
            const shres = shiftc32(self.getReg(a.rm), sh.t, @truncate(sh.n), self.psr.c);
            const res = addWithCarry32(~self.getReg(a.rn), shres.value, true);
            self.setReg(a.rd, res.v);
            if (a.S) {
                self.psr.n = res.v & 0x8000_0000 != 0;
                //self.psr.z = res.v == 0; ??
                self.psr.c = res.carry_out;
                self.psr.v = res.overflow;
            }
        }
    }

    test "rsbregT1" {}

    fn movregT3(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u4,
                rd: u4,
                _1: u4,
                //====
                _2: u4,
                S: bool,
                _3: u11,
            }, @bitCast(self.decoder.current));

            const res = self.getReg(a.rm);

            if (a.rd == 15) {
                self.aluWritePc(res);
            } else {
                self.setReg(a.rd, res);
                if (a.S) {
                    self.psr.n = res & 0x8000_0000 != 0;
                    self.psr.z = res == 0;
                }
            }
        }
    }

    test movregT3 {}

    fn lslimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            //TODO unnecessary
            const sh = decodeImmShift(0, (@as(u5, a.imm3) << 2) | a.imm2);

            const res = shiftc32(self.getReg(a.rm), .lsl, sh.n, self.psr.c);

            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test lslimmT2 {}

    fn lsrimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _1: u1,
                //====
                rn: u4,
                S: bool,
                _2: u11,
            }, @bitCast(self.decoder.current));
            const res = shiftc32(self.getReg(a.rm), .lsr, (@as(u5, a.imm3) << 2) | a.imm2, self.psr.c);
            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test lsrimmT2 {}

    fn asrimmT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const res = shiftc32(self.getReg(a.rm), .asr, (@as(u5, a.imm3) << 2) | a.imm2, self.psr.c);

            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test "asrimmT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rm: u4,
            typ: Shift,
            imm2: u2,
            rd: u4,
            imm3: u3,
            _0: u1,
            //====
            rn: u4,
            S: bool,
            _1: u11,
        });

        cpu.setAndExecCurrentInstr(.asrimmT2, @bitCast(a));
        try testing.expect(!cpu.psr.z);

        a.S = true;

        cpu.setAndExecCurrentInstr(.asrimmT2, @bitCast(a));
        try testing.expect(cpu.psr.z);

        a.rm = 1;
        a.rd = 2;

        a.imm3 = 0b111;
        a.imm2 = 0b11;

        cpu.setReg(a.rm, 0x8000_0000);
        cpu.setAndExecCurrentInstr(.asrimmT2, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_ffff);
    }

    fn rrxT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u4,
                rd: u4,
                imm3: u3,
                _1: u1,
                //====
                rn: u4,
                S: bool,
                _2: u11,
            }, @bitCast(self.decoder.current));
            const res = shiftc32(self.getReg(a.rm), .rrx, 1, self.psr.c);
            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test "rrxT1" {}

    fn rorimmT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            //TODO unnecessary
            const sh = decodeImmShift(3, (@as(u5, a.imm3) << 2) | a.imm2);

            const res = shiftc32(self.getReg(a.rm), .ror, sh.n, self.psr.c);

            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test "rorimmT1" {}

    fn lslregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const res = shiftc32(self.getReg(a.rn), .lsl, @truncate(self.getReg(a.rm)), self.psr.c);

            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test lslregT2 {}

    fn lsrregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                typ: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const res = shiftc32(self.getReg(a.rn), .lsr, @truncate(self.getReg(a.rm)), self.psr.c);

            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test lsrregT2 {}

    fn asrregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _1: u4,
                rd: u4,
                _2: u4,
                //====
                rn: u4,
                S: bool,
                _3: u11,
            }, @bitCast(self.decoder.current));
            const res = shiftc32(self.getReg(a.rn), .asr, @truncate(self.getReg(a.rm)), self.psr.c);
            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test "asrregT2" {
        try cpu.init(mem_buf[0..]);
        var a = std.mem.zeroes(packed struct(u32) { //
            rm: u4,
            _1: u4,
            rd: u4,
            _2: u4,
            //====
            rn: u4,
            S: bool,
            _3: u11,
        });

        cpu.setAndExecCurrentInstr(.asrregT2, @bitCast(a));
        try testing.expect(!cpu.psr.z);

        a.S = true;

        cpu.setAndExecCurrentInstr(.asrregT2, @bitCast(a));
        try testing.expect(cpu.psr.z);

        a.rn = 0;
        a.rm = 2;
        cpu.setReg(a.rm, 0xf00f);
        cpu.setReg(a.rn, 0x8000_0000);
        cpu.setAndExecCurrentInstr(.asrregT2, @bitCast(a));
        try testing.expect(cpu.getReg(a.rd) == 0xffff_0000);
    }

    fn rorregT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u4,
                rd: u4,
                imm3: u3,
                _1: u1,
                //====
                rn: u4,
                S: bool,
                _2: u11,
            }, @bitCast(self.decoder.current));
            const res = shiftc32(self.getReg(a.rn), .ror, @truncate(self.getReg(a.rm)), self.psr.c);
            self.setReg(a.rd, res.value);
            if (a.S) {
                self.psr.n = res.value & 0x8000_0000 != 0;
                self.psr.z = res.value == 0;
                self.psr.c = res.carry;
            }
        }
    }

    test rorregT2 {}

    fn sxthT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rd: u4,
                _0: u4,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));
            const rotated: i16 = @bitCast(@as(u16, @truncate(std.math.rotr(u32, self.getReg(a.rm), @as(u8, a.rotate) << 3))));
            self.setReg(a.rd, @bitCast(@as(i32, rotated)));
        }
    }

    test "sxthT2" {}

    fn uxthT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rd: u4,
                _0: u4,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));
            const rotated: u16 = @truncate(std.math.rotr(u32, self.getReg(a.rm), @as(u8, a.rotate) << 3));
            self.setReg(a.rd, rotated);
        }
    }

    test uxthT2 {}

    fn sxtbT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rd: u4,
                _0: u4,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));
            const rotated: i8 = @bitCast(@as(u8, @truncate(std.math.rotr(u32, self.getReg(a.rm), @as(u8, a.rotate) << 3))));
            self.setReg(a.rd, @bitCast(@as(i32, rotated)));
        }
    }

    test sxtbT2 {}

    fn uxtbT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));
            const rotated: u8 = @truncate(std.math.rotr(u32, self.getReg(a.rm), @as(u8, a.rotate) << 3));
            self.setReg(a.rd, rotated);
        }
    }

    test uxtbT2 {}

    fn revT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u4,
                rd: u4,
                imm3: u3,
                _1: u1,
                //====
                rm2: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            var bits = self.getReg(a.rm);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&bits))[0..4]);
            self.setReg(a.rd, bits);
        }
    }

    test "revT2" {}

    fn rev16T2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u4,
                rd: u4,
                imm3: u3,
                _1: u1,
                //====
                rm2: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));

            var bits = self.getReg(a.rm);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&bits))[0..2]);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&bits))[2..4]);
            self.setReg(a.rd, bits);
        }
    }

    test "rev16T2" {}

    fn rbitT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rm2: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            self.setReg(a.rd, @bitReverse(self.getReg(a.rm)));
        }
    }

    test "rbitT1" {}

    fn revshT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rm2: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            var r = self.getReg(a.rm);
            std.mem.reverse(u8, @as([*]u8, @ptrCast(&r))[0..2]);
            self.setReg(a.rd, @bitCast(@as(i32, @as(i16, @bitCast(@as(u16, @truncate(r)))))));
        }
    }

    test "revshT2" {}

    fn clzT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rd: u4,
                imm3: u3,
                _0: u1,
                //====
                rm2: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            self.setReg(a.rd, @clz(self.getReg(a.rm)));
        }
    }

    test "clzT1" {
        // pass
    }

    fn mlaT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u4,
                rd: u4,
                ra: u4,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            self.setReg(a.rd, self.getReg(a.rn) * self.getReg(a.rm) + self.getReg(a.ra));
        }
    }

    test "mlaT1" {}

    fn mulT2(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u4,
                rd: u4,
                _1: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            self.setReg(a.rd, self.getReg(a.rn) * self.getReg(a.rm));
        }
    }

    test "mulT2" {}

    fn mlsT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _0: u4,
                rd: u4,
                ra: u4,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            self.setReg(a.rd, self.getReg(a.ra) - (self.getReg(a.rn) * self.getReg(a.rm)));
        }
    }

    test mlsT1 {}

    fn smullT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _1: u4,
                rdHi: u4,
                rdLo: u4,
                //====
                rn: u4,
                S: bool,
                _2: u11,
            }, @bitCast(self.decoder.current));

            const res = @as(i64, @as(i32, @bitCast(self.getReg(a.rn)))) *
                @as(i64, @as(i32, @bitCast(self.getReg(a.rm))));

            self.setReg(a.rdHi, @bitCast(@as(i32, @truncate(res >> 32))));
            self.setReg(a.rdLo, @bitCast(@as(i32, @truncate(res))));
        }
    }

    test smullT1 {}

    fn sdivT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _1: u4,
                rd: u4,
                _2: u4,
                //====
                rn: u4,
                _3: u12,
            }, @bitCast(self.decoder.current));

            const op2: i32 = @bitCast(self.getReg(a.rm));

            if (op2 == 0) {
                if (self.integerZeroDivideTrappingEnabled()) {
                    //TODO
                } else {
                    self.setReg(a.rd, 0);
                }
            } else {
                self.setReg(a.rd, @bitCast(@divTrunc(@as(i32, @bitCast(self.getReg(a.rn))), op2)));
            }
        }
    }

    test sdivT1 {}

    fn umullT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rdHi: u4,
                rdLo: u4,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const res = @as(u64, self.getReg(a.rn)) *
                @as(u64, self.getReg(a.rm));

            self.setReg(a.rdHi, @truncate(res >> 32));
            self.setReg(a.rdLo, @truncate(res));
        }
    }

    test "umullT1" {}

    fn udivT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rd: u4,
                ra: u4,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const op2 = self.getReg(a.rm);

            if (op2 == 0) {
                if (self.integerZeroDivideTrappingEnabled()) {
                    //TODO
                } else {
                    self.setReg(a.rd, 0);
                }
            } else {
                self.setReg(a.rd, @divTrunc(self.getReg(a.rn), op2));
            }
        }
    }

    test "udivT1" {}

    fn smlalT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                _1: u4,
                rdHi: u4,
                rdLo: u4,
                //====
                rn: u4,
                S: bool,
                _2: u11,
            }, @bitCast(self.decoder.current));

            const res = (@as(i64, @as(i32, @bitCast(self.getReg(a.rn)))) *
                @as(i64, @as(i32, @bitCast(self.getReg(a.rm))))) +
                @as(i64, @bitCast(((@as(u64, self.getReg(a.rdHi))) << 32) | (@as(u64, self.getReg(a.rdLo)))));

            self.setReg(a.rdHi, @bitCast(@as(i32, @truncate(res >> 32))));
            self.setReg(a.rdLo, @bitCast(@as(i32, @truncate(res))));
        }
    }

    test smlalT1 {}

    fn umlalT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                rm: u4,
                rotate: u2,
                imm2: u2,
                rdHi: u4,
                rdLo: u4,
                //====
                rn: u4,
                S: bool,
                _1: u11,
            }, @bitCast(self.decoder.current));

            const res = @as(u64, self.getReg(a.rn)) *
                @as(u64, self.getReg(a.rm)) +
                (@as(u64, self.getReg(a.rdHi)) << 32) | (@as(u64, self.getReg(a.rdLo)));

            self.setReg(a.rdHi, @truncate(res >> 32));
            self.setReg(a.rdLo, @truncate(res));
        }
    }

    test umlalT1 {}

    fn svcT1(self: *Cpu) void {
        _ = self;
        //TODO
    }

    fn bT1(self: *Cpu) void {
        if (self.conditionPassed()) {
            const imm32 = @as(i32, @as(i8, @bitCast(@as(u8, @truncate(self.decoder.current & 0xff)) << 1)));
            self.branchWritePC(self.getPC() + @as(u32, @bitCast(imm32)));
        }
    }

    test "bT1" {
        try cpu.init(mem_buf[0..]);
        cpu.PC = 0;
        cpu.setAndExecCurrentInstr(.bT1, 0x0_80);
        try testing.expect(cpu.PC == 2);

        cpu.PC = 0;
        cpu.psr.z = true;
        cpu.setAndExecCurrentInstr(.bT1, 0x0_40);
        try testing.expect(cpu.PC == (4 + (0xffff_ff80)));
    }

    fn strbt(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _1: u4,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            self.writeMemU_Unpriv(u8, self.getReg(a.rn) + a.imm8, @truncate(self.getReg(a.rt)));
        }
    }

    test "strbt" {}

    fn strt(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _1: u4,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            self.writeMemU_Unpriv(u32, self.getReg(a.rn) + a.imm8, @truncate(self.getReg(a.rt)));
        }
    }

    test "strt" {}

    fn strht(self: *Cpu) void {
        if (self.conditionPassed()) {
            const a = @as(packed struct(u32) { //
                imm8: u8,
                _1: u4,
                rt: u4,
                //====
                rn: u4,
                _2: u12,
            }, @bitCast(self.decoder.current));
            self.writeMemU_Unpriv(u16, self.getReg(a.rn) + a.imm8, @truncate(self.getReg(a.rt)));
        }
    }

    test "strht" {}

    fn exec(self: *Cpu, instr: Instr) void {
        std.debug.print("instr: {} {x}\n", .{ instr, self.PC });
        switch (instr) {
            //else => unreachable,
            .strt => self.strt(),
            .strht => self.strht(),
            .strbt => self.strbt(),
            .unpredictable => {},
            .rorimmT1 => self.rorimmT1(),
            .ldrsbimmT2 => self.ldrsbimmT2(),
            .ldrblitT1 => self.ldrblitT1(),
            .sbfxT1 => self.sbfxT1(),
            .ldrshimmT2 => self.ldrshimmT2(),
            .ldrtT1 => self.ldrtT1(),
            .bT1 => self.bT1(),
            .svc => self.svcT1(),
            .unknown => self.undefined(),
            .umlalT1 => self.umlalT1(),
            .smlalT1 => self.smlalT1(),
            .udivT1 => self.udivT1(),
            .umullT1 => self.umullT1(),
            .sdivT1 => self.sdivT1(),
            .smullT1 => self.smullT1(),
            .mlsT1 => self.mlsT1(),
            .mulT2 => self.mulT2(),
            .mlaT1 => self.mlaT1(),
            .clzT1 => self.clzT1(),
            .revshT2 => self.revshT2(),
            .rbitT1 => self.rbitT1(),
            .rev16T2 => self.rev16T2(),
            .revT2 => self.revT2(),
            .uxtbT2 => self.uxtbT2(),
            .sxtbT2 => self.sxtbT2(),
            .uxthT2 => self.uxthT2(),
            .sxthT2 => self.sxthT2(),
            .rorregT2 => self.rorregT2(),
            .asrregT2 => self.asrregT2(),
            .lsrregT2 => self.lsrregT2(),
            .lslregT2 => self.lslregT2(),
            .rrxT1 => self.rrxT1(),
            .asrimmT2 => self.asrimmT2(),
            .lsrimmT2 => self.lsrimmT2(),
            .lslimmT2 => self.lslimmT2(),
            .movregT3 => self.movregT3(),
            .rsbregT1 => self.rsbregT1(),
            .cmpregT3 => self.cmpregT3(),
            .subregT2 => self.subregT2(),
            .sbcregT2 => self.sbcregT2(),
            .adcregT2 => self.adcregT2(),
            .cmnregT2 => self.cmnregT2(),
            .addregT3 => self.addregT3(),
            .tegregT1 => self.teqregT1(),
            .eorregT2 => self.eorregT2(),
            .mvnregT2 => self.mvnregT2(),
            .ornregT1 => self.ornregT1(),
            .orrregT2 => self.orrregT2(),
            .bicregT2 => self.bicregT2(),
            .tstregT2 => self.tstregT2(),
            .andregT2 => self.andregT2(),
            .strregT2 => self.strregT2(),
            .strimmT4 => self.strimmT4(),
            .strimmT3 => self.strimmT3(),
            .strhregT2 => self.strhregT2(),
            .strhimmT2 => self.strhimmT2(),
            .strhimmT3 => self.strhimmT3(),
            .strbregT2 => self.strbregT2(),
            .strbimmT2 => self.strbimmT2(),
            .strbimmT3 => self.strbimmT3(),
            .pldimmT1 => {}, // we dont do that here
            .ldrsbregT2 => self.ldrsbregT2(),
            .ldrsblitT1 => self.ldrsblitT1(),
            .ldrsbtT1 => self.ldrsbtT1(),
            .ldrsbimmT1 => self.ldrsbimmT1(),
            .ldrbregT2 => self.ldrbregT2(),
            .ldrbtT1 => self.ldrbtT1(),
            .ldrbimmT3 => self.ldrbimmT3(),
            .ldrbimmT2 => self.ldrbimmT2(),
            .ldrshregT2 => self.ldrshregT2(),
            .ldrshlitT1 => self.ldrshlitT1(),
            .ldrshtT1 => self.ldrshtT1(),
            .ldrshimmT1 => self.ldrshimmT1(),
            .ldrhregT2 => self.ldrhregT2(),
            .ldrhlitT1 => self.ldrhlitT1(),
            .ldrhtT1 => self.ldrhtT1(),
            .ldrhimmT3 => self.ldrhimmT3(),
            .ldrhimmT2 => self.ldrhimmT2(),
            .ldrlitT2 => self.ldrlitT2(),
            .ldrregT2 => self.ldrregT2(),
            .ldrimmT4 => self.ldrimmT4(),
            .ldrimmT3 => self.ldrimmT3(),
            .ldrexhT1 => self.ldrexhT1(),
            .ldrexbT1 => self.ldrexbT1(),
            .tbbT1 => self.tbbT1(),
            .strexhT1 => self.strexhT1(),
            .strexbT1 => self.strexbT1(),
            .strdimmT1 => self.strdimmT1(),
            .ldrdimmT1 => self.ldrdimmT1(),
            .ldrdlitT1 => self.ldrdlitT1(),
            .ldrexT1 => self.ldrexT1(),
            .strexT1 => self.strexT1(),
            .ldmdbT1 => self.ldmdbT1(),
            //TODO pushT3
            .pushT2 => self.pushT2(),
            .stmdbT1 => self.stmdbT1(),
            //TODO popT3
            .popT2 => self.popT2(),
            .ldmT2 => self.ldmT2(),
            .stmT2 => self.stmT2(),
            .isbT1 => self.isb(),
            .dmbT1 => self.dmb(),
            .dsbT1 => self.dsb(),
            .clrexT1 => self.clrex(),
            .dbgT1 => self.dbg(),
            .sev, .sevT2 => self.sev(),
            .wfi, .wfiT2 => self.wfi(),
            .wfe, .wfeT2 => self.wfe(),
            .yield, .yieldT2 => self.yield(),
            .nop, .nopT2 => self.nop(),
            .blT1 => self.blT1(),
            .undefined => self.undefined(),
            .mrsT1 => self.mrsT1(),
            .msrT1 => self.msrT1(),
            .bT4 => self.bT4(),
            .bT3 => self.bT3(),
            .ubfxT1 => self.ubfxT1(),
            .usatT1 => self.usatT1(),
            .bfiT1 => self.bfiT1(),
            .bfcT1 => self.bfcT1(),
            .ssatT1 => self.ssatT1(),
            .movtT1 => self.movtT1(),
            .subimmT4 => self.subimmT4(),
            .movimmT3 => self.movimmT3(),
            .adrT2 => self.adrT2(),
            .adrT3 => self.adrT3(),
            .addimmT4 => self.addimmT4(),
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
            .asrimmT1 => self.asrimmT1(),
            .lsrimmT1 => self.lsrimmT1(),
            .lslimmT1 => self.lslimmT1(),
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
            .subspimmT1 => subspimmT1(self),
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

            //else => unreachable,
        }

        switch (instr) {
            .it => {},
            else => self.psr.advanceIT(),
        }

        if (self.decoder.on32) {
            self.PC += 4;
        } else {
            self.PC += 2;
        }
    }
};

var cpu = Cpu{};

// 32mb memory
var mem_buf: [1024 * 1024 * 32]u8 = undefined;

fn testStuff(config_path: []const u8) !void {
    std.debug.print("testing with file: {s}........\n", .{config_path});

    const file = std.fs.cwd().openFile(config_path, .{}) catch {
        std.debug.print("could not open file: {s}\n", .{config_path});
        std.process.exit(1);
    };
    defer file.close();

    const contents = try file.readToEndAlloc(gpa.allocator(), std.math.maxInt(u16));
    defer gpa.allocator().free(contents);

    const F = struct { //
        Z: bool,
        C: bool,
        V: bool,
        N: bool,
        Q: bool,
        T: bool,
        A: bool,
    };
    const object = try std.json.parseFromSlice(struct { //
        program: []const u8,
        regsBefore: [14]u32,
        flagsBefore: F,
        regsAfter: [14]u32,
        flagsAfter: F,
        cycles: u8,
    }, gpa.allocator(), contents, .{});

    const asm_path = "C:\\Users\\murim\\OneDrive\\Desktop\\code\\src\\prog.s";

    var asm_file = try std.fs.createFileAbsolute(asm_path, .{
        .truncate = true,
    });

    defer asm_file.close();

    const source_file = std.fs.cwd().openFile(object.value.program, .{}) catch {
        std.debug.print("failed to open program file.\n", .{});
        std.process.exit(1);
    };

    const copy_size = (try source_file.stat()).size;
    const n = try source_file.copyRange(0, asm_file, 0, copy_size);

    if (n != copy_size) {
        std.debug.print("failed to copy program.", .{});
        std.process.exit(1);
    }

    var child = std.process.Child.init(&.{ "zig", "build" }, gpa.allocator());
    child.stderr_behavior = .Pipe;
    child.stdout_behavior = .Pipe;

    try child.spawn();

    var stderr = try std.ArrayListUnmanaged(u8).initCapacity(gpa.allocator(), 4096);
    var stdout = try std.ArrayListUnmanaged(u8).initCapacity(gpa.allocator(), 4096);

    try child.collectOutput(gpa.allocator(), &stdout, &stderr, 4096);

    const term = try child.wait();

    if (term.Exited != 0) {
        std.debug.print("zig build failed: {s}\n", .{stderr.items});
        std.process.exit(1);
    }

    try cpu.init(mem_buf[0..]);
    try cpu.loadElf(elf_path);

    for (object.value.regsBefore, 0..) |r, i| {
        cpu.setReg(i, r);
    }

    cpu.psr.n = object.value.flagsBefore.N;
    cpu.psr.c = object.value.flagsBefore.C;
    cpu.psr.a = object.value.flagsBefore.A;
    cpu.psr.q = object.value.flagsBefore.Q;
    cpu.psr.v = object.value.flagsBefore.V;
    cpu.psr.t = object.value.flagsBefore.T;
    cpu.psr.z = object.value.flagsBefore.Z;

    for (0..object.value.cycles) |_| {
        const i = cpu.fetch();
        cpu.exec(i);
    }

    for (object.value.regsAfter, 0..) |expected, i| {
        const actual = cpu.getReg(i);
        if (actual != expected) {
            std.debug.print("wrong register {} expected: {} found: {}\n", .{ i, expected, actual });
            cpu.printRegisters();
            std.process.exit(1);
        }
    }

    if (cpu.psr.n != object.value.flagsAfter.N or
        cpu.psr.c != object.value.flagsAfter.C or
        cpu.psr.a != object.value.flagsAfter.A or
        cpu.psr.q != object.value.flagsAfter.Q or
        cpu.psr.v != object.value.flagsAfter.V or
        cpu.psr.t != object.value.flagsAfter.T or
        cpu.psr.z != object.value.flagsAfter.Z)
    {
        std.debug.print("wrong flags expected:\n    {}\nfound:\n    {}\n", .{ object.value.flagsAfter, F{
            .A = cpu.psr.a,
            .C = cpu.psr.c,
            .N = cpu.psr.n,
            .Q = cpu.psr.q,
            .T = cpu.psr.t,
            .V = cpu.psr.v,
            .Z = cpu.psr.z,
        } });
        std.process.exit(1);
    }

    std.debug.print("[ok]\n", .{});
    std.process.exit(0);
}

var gpa = std.heap.GeneralPurposeAllocator(.{}){};

pub fn main() !void {
    try cpu.init(mem_buf[0..]);
    cpu.takeReset();
    //try cpu.loadElf(elf_path);

    while (true)
    //for (0..45) |_|
    {
        const i = cpu.fetch();
        //std.debug.print("--: {}\n", .{i});
        //std.debug.print("last in it: {}\n", .{cpu.psr.getIT().last()});
        cpu.exec(i);

        //cpu.printRegisters();
    }
}

pub fn maintt() !void {
    var args = try std.process.ArgIterator.initWithAllocator(gpa.allocator());
    _ = args.next();

    if (args.next()) |arg| {
        if (std.mem.eql(u8, arg, "test")) {
            if (args.next()) |arg2| {
                try testStuff(arg2[0..]);
            } else {
                std.debug.print("Expects path to config!!!\n", .{});
            }
        }
        return;
    }

    try cpu.init(mem_buf[0..]);
    try cpu.loadElf(elf_path);

    while (true)
    //for (0..45) |_|
    {
        const i = cpu.fetch();
        //std.debug.print("--: {}\n", .{i});
        //std.debug.print("last in it: {}\n", .{cpu.psr.getIT().last()});
        cpu.exec(i);

        //cpu.printRegisters();
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
    lslimmT1,
    lsrimmT1,
    asrimmT1,
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
    ldrdlitT1,
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
    ldrsbimmT2,
    ldrsbtT1,
    ldrsblitT1,
    ldrsbregT2,
    pldimmT1,

    strbimmT3,
    strbt,
    strbregT2,
    strbimmT2,
    strhimmT2,
    strhimmT3,
    strht,
    strhregT2,
    strimmT3,
    strimmT4,
    strt,
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

    lslregT2,
    lsrregT2,
    asrregT2,
    rorregT2,
    sxthT2,
    uxthT2,
    sxtbT2,
    uxtbT2,

    revT2,
    rev16T2,
    rbitT1,
    revshT2,
    clzT1,

    mlaT1,
    mulT2,
    mlsT1,

    smullT1,
    sdivT1,
    umullT1,
    udivT1,
    smlalT1,
    umlalT1,
};

pub const Decoder = struct {
    const MISC: u32 = 0b1011_0000_0000_0000;
    const COND_BRANCH_SUPERV = 0b1101_0000_0000_0000;
    const UCOND_BRANCH = 0b1110_0000_0000_0000;

    stream: std.io.FixedBufferStream([]u8),
    endian: std.builtin.Endian,

    current: u32 = 0,
    current_instr: Instr = .unknown,

    on32: bool,

    pub fn init(endian: std.builtin.Endian, memory: []u8) !Decoder {
        return .{ //
            .on32 = false,
            .endian = endian,
            .stream = std.io.fixedBufferStream(memory),
        };
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

        if (a.op1 >> 1 == 0 and a.op2 == 0b11) return .ldrdimmT1;

        if (a.op1 >> 1 == 1 and a.op2 & 1 == 1) return .ldrdlitT1;

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
        if (a.op1 == 0b10 and a.op2 & 0b100000 != 0 and a.op2 & 0b100 != 0 and a.rn != 0xf and a.rt != 0xf) return .ldrsbimmT2;
        if (a.op1 == 0b10 and a.op2 >> 2 == 0b1100 and a.rn != 0xf and a.rt != 0xf) return .ldrsbimmT2;

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
            0 => if (a.op2 & 0b100000 != 0) (if (((w >> 8) & 0b1111) == 0b1110) .strbt else .strbimmT3) else .strbregT2,
            0b100 => .strbimmT2,
            0b101 => .strhimmT2,
            0b1 => if (a.op2 & 0b100000 != 0) (if (((w >> 8) & 0b1111) == 0b1110) .strht else .strhimmT3) else .strhregT2,
            0b110 => .strimmT3,
            0b10 => if (a.op2 & 0b100000 != 0) (if (((w >> 8) & 0b1111) == 0b1110) .strt else .strimmT4) else .strregT2,
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

    fn dataProcReg(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u4,
            op2: u4,
            _2: u8,
            //===
            rn: u4,
            op1: u4,
            _3: u8,
        }, @bitCast(w));

        return if (a.op2 == 0)
            switch (a.op1 >> 1) {
                0 => .lslregT2,
                1 => .lsrregT2,
                2 => .asrregT2,
                3 => .rorregT2,
                else => unreachable,
            }
        else switch (a.op1) {
            0 => if (a.op2 & 0b1000 != 0 and a.rn == 0xf) .sxthT2 else unreachable,
            1 => if (a.op2 & 0b1000 != 0 and a.rn == 0xf) .uxthT2 else unreachable,
            0b100 => if (a.op2 & 0b1000 != 0 and a.rn == 0xf) .sxtbT2 else unreachable,
            0b101 => if (a.op2 & 0b1000 != 0 and a.rn == 0xf) .uxtbT2 else unreachable,
            else => if (a.op1 >> 2 == 0b10 and a.op2 >> 2 == 0b10) block: {
                const b = @as(packed struct(u32) { //
                    _1: u4,
                    op2: u2,
                    _2: u10,
                    //===
                    _3: u4,
                    op1: u2,
                    _4: u10,
                }, @bitCast(w));

                if (w & 0xf000 != 0xf000) break :block .undefined;

                break :block switch (b.op1) {
                    1 => switch (b.op2) {
                        0 => .revT2,
                        1 => .rev16T2,
                        2 => .rbitT1,
                        3 => .revshT2,
                    },
                    0b11 => switch (b.op2) {
                        0 => .clzT1,
                        else => unreachable,
                    },
                    else => unreachable,
                };
            } else unreachable,
        };
    }

    fn multmultacc(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u4,
            op2: u2,
            _2: u6,
            ra: u4,
            //===
            _3: u4,
            op1: u3,
            _4: u9,
        }, @bitCast(w));

        return switch (a.op1) {
            0 => switch (a.op2) {
                0 => if (a.ra != 0xf) .mlaT1 else .mulT2,
                1 => .mlsT1,
                else => unreachable,
            },
            else => unreachable,
        };
    }

    fn longmullongmullaccdiv(w: u32) Instr {
        const a = @as(packed struct(u32) { //
            _1: u4,
            op2: u4,
            _2: u8,
            //===
            _3: u4,
            op1: u3,
            _4: u9,
        }, @bitCast(w));

        return switch (a.op1) {
            0 => switch (a.op2) {
                0 => .smullT1,
                else => unreachable,
            },
            1 => switch (a.op2) {
                0xf => .sdivT1,
                else => unreachable,
            },
            2 => switch (a.op2) {
                0 => .umullT1,
                else => unreachable,
            },
            3 => switch (a.op2) {
                0xf => .udivT1,
                else => unreachable,
            },
            4 => switch (a.op2) {
                0 => .smlalT1,
                else => unreachable,
            },
            0b110 => switch (a.op2) {
                0 => .umlalT1,
                else => unreachable,
            },
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
        } else if (wh >> 8 == 0b111_1101_0 and wl & 0xf000 == 0xf000) {
            return dataProcReg(self.current);
        } else if (wh >> 7 == 0b111_1101_10 and wl & 0b11000000 == 0) {
            return multmultacc(self.current);
        } else if (wh >> 7 == 0b111_1101_11) {
            return longmullongmullaccdiv(self.current);
        }
        return .unknown;
    }

    pub fn decode(self: *Decoder, ip: usize) Instr {
        self.stream.seekTo(ip) catch unreachable;
        const word = self.getWord() catch unreachable;
        //std.debug.print("seq: {b}\n", .{word});
        if (is32bit(word)) {
            self.on32 = true;
            self.current_instr = self.instr32(word);
            return self.current_instr;
        }

        self.on32 = false;

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
        else if (word >> 10 == 0b10001) specDataBranch(word) //
            else if (word >> 10 == 0b10000) dataProc(word) //
            else if (word >> 14 == 0b00) shaddsubmovcmp(word) //
            else if (word >> 11 == 0b1001) .ldrlitT1 //
            else if (word >> 11 == 0b10101) .addspimmT1 //
            else if (word >> 11 == 0b11000) .stmT1 //
            else if (word >> 11 == 0b11001) .ldmT1 //
            else if (word >> 11 == 0b10100) .adrT1 else unreachable;

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
                0 => .lslimmT1,
                1 => .lsrimmT1,
                2 => .asrimmT1,
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
        const mask: u16 = 0b00011000_00000000;
        const mask2: u16 = 0b11100000_00000000;
        if (word & mask == 0) return false;
        return word & mask2 == mask2;
    }
};
