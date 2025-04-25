export var stack: [1024 * 16]u8 align(4) linksection(".bss.stack") = undefined;
extern const __stack_stop: u32;

extern var isr_vector: [2]u32;

const PSR = packed struct(u32) {
    _1: u27 = 0,
    q: bool = false,
    v: bool = false,
    c: bool = false,
    z: bool = false,
    n: bool = false,
};

pub export fn _start() callconv(.naked) void {
    asm volatile ("bl #foo");
}

pub export fn usageFaultHandler() void {
    asm volatile ("wfi");
}

pub export fn systickHandler() void {
    asm volatile ("wfi");
}

pub export fn hardFaultHandler() void {
    while (true) {
        asm volatile ("nop");
        asm volatile ("nop");
        asm volatile ("nop");
        asm volatile ("nop");
        asm volatile ("nop");
        asm volatile ("nop");
        asm volatile ("nop");
        print("hard", .{});
        asm volatile("yield");
    }
}

pub export fn memHandler() void {
    while (true) {
        asm volatile ("yield");
    }
}

//var a: [32]u8 = undefined;

const SYST_CSR = packed struct(u32) {
    const addr = 0xE000E010;
    /// 0: the counter is disabled
    ///  1: the counter will operate in a multi-shot manner.
    enable: bool = false,
    /// If 1, counting down to 0 will cause the SysTick exception to
    /// be pended. Clearing the SysTick Current Value register by a
    /// register write in software will not cause SysTick to be
    /// pended.
    tickint: bool = false,
    /// 0: clock source is (optional) external reference clock
    ///  1: core clock used for SysTick
    ///  If no external clock provided, this bit will read as 1 and
    /// ignore writes.
    clcksource: bool = false,
    _1: u13 = 0,
    /// Returns 1 if timer counted to 0 since last time this register
    /// was read. COUNTFLAG is set by a count transition from 1
    /// => 0. COUNTFLAG is cleared on read or by a write to the
    /// Current Value register.
    countflag: bool = false,
    _2: u15 = 0,
};

const SYST_RVR = packed struct(u32) {
    const addr = 0xE000E014;
    /// Value to load into the Current Value register when the counter
    /// reaches 0.
    reload: u24,
    _1: u8,
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

const NVIC_ISER = packed struct(u32) {
    const addr = 0xE000E100;
    /// Enable one or more interrupts within a group of 32. Each bit
    /// represents an interrupt number from N to N+31 (starting at
    /// interrupt 0, 32, 64, etc).
    /// Writing a 1 will enable the associated interrupt.
    /// Writing a 0 has no effect.
    /// The register reads back with the current enable state.
    back: u32 = 0,

    fn check(self: @This(), bit: u5) bool {
        const mask = std.math.shl(u32, 1, bit);
        return self.back & mask == mask;
    }

    fn set(self: *@This(), bit: u5) void {
        const mask = std.math.shl(u32, 1, bit);
        self.back = self.back | mask;
    }

    fn clr(self: *@This(), bit: u5) void {
        const mask = std.math.shl(u32, 1, bit);
        self.back = self.back & ~mask;
    }
};

const NVIC_ICER = packed struct(u32) {
    const addr = 0xE000E180;
    /// Disable one or more interrupts within a group of 32. Each bit
    /// represents an interrupt number from N to N+31 (starting at
    /// interrupt 0, 32, 64, etc).
    /// Writing a 1 will disable the associated interrupt.
    ///  Writing a 0 has no effect.
    ///  The register reads back with the current enable state.
    back: u32 = 0,

    fn check(self: @This(), bit: u5) bool {
        const mask = std.math.shl(u32, 1, bit);
        return self.back & mask == mask;
    }

    fn set(self: *@This(), bit: u5) void {
        const mask = std.math.shl(u32, 1, bit);
        self.back = self.back | mask;
    }

    fn clr(self: *@This(), bit: u5) void {
        const mask = std.math.shl(u32, 1, bit);
        self.back = self.back & ~mask;
    }
};

const syst_csr: *SYST_CSR = @ptrFromInt(SYST_CSR.addr);
const syst_rvr: *SYST_RVR = @ptrFromInt(SYST_RVR.addr);
const aircr: *AIRCR = @ptrFromInt(AIRCR.addr);

const SHPR: *[12]u8 = @ptrFromInt(0xE000ED18);

const stir: *STIR = @ptrFromInt(STIR.addr);
const ccr: *CCR = @ptrFromInt(CCR.addr);

const nvic_icer: *NVIC_ICER = @ptrFromInt(NVIC_ICER.addr);
const nvic_iser: *NVIC_ISER = @ptrFromInt(NVIC_ISER.addr);

const UART = struct {
    const base = 0x4000_0000;
    const DR = packed struct(u32) {
        const offset = 0;
        data: u8,
        _1: u24,
    };

    const UARTCR = packed struct(u32) {
        const offset = 0x030;
        uarten: bool,
        _1: u7,
        txe: bool,
        rxe: bool,
        _2: u22,
    };

    const UARTIMSC = packed struct(u32) {
        const offset = 0x038;
        _1: u4,
        rxim: bool,
        txim: bool,
        _2: u26,
    };
};

const boo: *u8 = @ptrFromInt(0xe000_0000);

const uartdr: *UART.DR = @ptrFromInt(UART.base+UART.DR.offset);
const uartcr: *UART.UARTCR = @ptrFromInt(UART.base+UART.UARTCR.offset);
const uartmsc: *UART.UARTIMSC = @ptrFromInt(UART.base+UART.UARTIMSC.offset);

fn writeChar(char:u8) void {
    uartdr.data = char;
}

fn write(_: void, buf: []const u8) !usize {
    for(buf) |by| writeChar(by);
    return buf.len;
}

const Writer = std.io.GenericWriter(void, error{}, write){
    .context = {}
};

fn print(comptime fmt: []const u8, args: anytype) void {
    std.fmt.format(Writer, fmt, args) catch unreachable;
}

var arr = "hello world";

pub fn digits2(value: u8) [2]u8 {
    return "00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899"[value * 2 ..][0..2].*;
}

export fn foo() void {

    uartcr.uarten = true;
    uartcr.rxe = true;
    uartcr.txe = true;

    asm volatile ("svc 0");




    //while (true) {
    //    asm volatile ("wfi");
    //    //uartdr.data = 'A';
    //}
    
    var buf:[64] u8 = undefined;
    _ = std.fmt.bufPrint(buf[0..], "one {any} one", .{arr[0..3]}) catch {
        unreachable;
    };
    _ = write({}, buf[0..]) catch unreachable;

    asm volatile ("yield");
}
var kkk:u8 = 0;
pub export fn interruptHandler() void {
   var a = uartdr.data;
    a += 90;
    kkk = a;
}


instr: cpu.Instr.blT1 af6e
instr: cpu.Instr.pushT1 93ec
instr: cpu.Instr.movregT1 93ee
instr: cpu.Instr.subspimmT1 93f0
instr: cpu.Instr.strimmT2 93f2
instr: cpu.Instr.strimmT2 93f4
instr: cpu.Instr.uxtbT1 93f6
instr: cpu.Instr.strbimmT3 93f8
instr: cpu.Instr.addregT1 93fc
instr: cpu.Instr.uxtbT1 93fe
instr: cpu.Instr.subregT1 9400
instr: cpu.Instr.it 9402
instr: cpu.Instr.movimmT1 9404
instr: cpu.Instr.movregT1 9406
instr: cpu.Instr.strimmT2 9408
instr: cpu.Instr.cmpregT1 940a
instr: cpu.Instr.bT1 940c
instr: cpu.Instr.bT2 940e

pub export fn svcHandler() void {
    nvic_iser.set(0);
    //syst_rvr.reload = 10;
    //syst_csr.tickint = true;
    //syst_csr.enable = true;
}

pub fn panic(message: []const u8, stack_trace: ?*std.builtin.StackTrace, n: ?usize) noreturn {
    //_ = message;
    _ = stack_trace;
    _ = n;

    //if (std.mem.eql(u8, message, "pass")) {
    //    asm volatile ("wfi");
    //} else {
    //    asm volatile ("wfe");
    //}
    _ = write({}, message) catch unreachable;
    while (true) {
        asm volatile ("yield");
    }
}

export var uArray = [1]u8{0xdd} ** 1000;

export var uArray2 = [1]u8{0xff} ** 1000;

export fn arrayAdd() void {}

// a1-a4 => caller saved r0-r3
// v1-v5, v7, v8 => callee saved

fn adcregT1() void {
    var psr: PSR = undefined;
    var res: u32 = undefined;

    //============================================

    psr = PSR{ .c = false, .n = true, .v = true, .z = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\ mov r0, #0 
        \\ adcs.n r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 0);

    expect(!psr.n);
    expect(!psr.c);
    expect(psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //============================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\ mov r0, #1024
        \\ adcs.n r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 1025);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //===========================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\mov r0, #0
        \\ adc.n r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 1);

    expect(!psr.n);
    expect(psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);
    //==================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #255
        \\mov r0, #0
        \\ adcs.n r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 256);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //==================================

    //0b111_1111_1111;

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #2047
        \\ mov r0, #0
        \\ adcs.n r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 2048);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //==================================

}

fn adcregT2() void {
    var psr: PSR = undefined;
    var res: u32 = undefined;

    //============================================

    psr = PSR{ .c = false, .n = true, .v = true, .z = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\ mov r0, #0 
        \\ adcs r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 0);

    expect(!psr.n);
    expect(!psr.c);
    expect(psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //============================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\ mov r0, #1024
        \\ adcs r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 1025);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //===========================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\mov r0, #0
        \\ adc r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 1);

    expect(!psr.n);
    expect(psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);
    //==================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #255
        \\mov r0, #0
        \\ adcs r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 256);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //==================================

    //0b111_1111_1111;

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #2047
        \\ mov r0, #0
        \\ adcs r8, r0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 2048);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //==================================

}

fn adcimmT1() void {
    var psr: PSR = undefined;
    var res: u32 = undefined;

    //============================================

    psr = PSR{ .c = false, .n = true, .v = true, .z = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\ adcs r8, #0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 0);

    expect(!psr.n);
    expect(!psr.c);
    expect(psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //============================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\ adcs r8, #1024
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 1025);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //===========================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #0
        \\ adc r8, #0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 1);

    expect(!psr.n);
    expect(psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);
    //==================================

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #255
        \\ adcs r8, #0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 256);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //==================================

    //0b111_1111_1111;

    psr = PSR{ .c = true };

    asm volatile (
        \\ mov r0, %[psr]
        \\ msr apsr, r0
        \\ eor r0, r0
        :
        : [psr] "{r0}" (psr),
    );

    res = asm volatile (
        \\ mov r8, #2047
        \\ adcs r8, #0
        : [o] "={r8}" (-> u32),
    );

    psr = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(res == 2048);

    expect(!psr.n);
    expect(!psr.c);
    expect(!psr.z);
    expect(!psr.q);
    expect(!psr.v);

    //==================================

}

fn baz() void {

    //asm volatile ("push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r14}");

    asm volatile (
        \\ eor r0, r0
        \\ msr apsr, r0
    );

    asm volatile (
        \\ cmp r0, #1
    );

    const psr: PSR = @bitCast(asm volatile (
        \\ mrs r0, apsr
        : [out] "={r0}" (-> u32),
    ));

    expect(psr.n);

    //asm volatile ("pop {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r14}");
}

const std = @import("std");

fn expect(v: bool) void {
    if (v) {
        asm volatile ("wfi");
    } else {
        @panic("");
    }
}


