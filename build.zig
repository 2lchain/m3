const std = @import("std");
const Build = std.Build;
const Target = std.Target;

// Although this function looks imperative, note that its job is to
// declaratively construct a build graph that will be executed by an external
// runner.
pub fn build(b: *Build) void {
    // Standard target options allows the person running `zig build` to choose
    // what target to build for. Here we do not override the defaults, which
    // means any target is allowed, and the default is native. Other options
    // for restricting supported target set are available.
    //const target = b.standardTargetOptions(.{});

    


    const query = Target.Query{
        .cpu_arch = Target.Cpu.Arch.thumb,
        .cpu_model = Target.Query.CpuModel{.explicit = &Target.arm.cpu.cortex_m3 },
        //.cpu_features_add = features,
        //.cpu_features_sub = unfeatures,
        .os_tag = .freestanding,
        .abi = .none
    };

    const target = b.resolveTargetQuery(query);

    //const target = b.

    // Standard optimization options allow the person running `zig build` to select
    // between Debug, ReleaseSafe, ReleaseFast, and ReleaseSmall. Here we do not
    // set a preferred release mode, allowing the user to decide how to optimize.
    //const optimize = b.standardOptimizeOption(.{
    //    .preferred_optimize_mode = .ReleaseSmall
    //});



    // We will also create a module for our other entry point, 'main.zig'.
    const exe_mod = b.createModule(.{
        // `root_source_file` is the Zig "entry point" of the module. If a module
        // only contains e.g. external object files, you can make this `null`.
        // In this case the main source file is merely a path, however, in more
        // complicated build scripts, this could be a generated file.
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = .Debug,
    });

    exe_mod.addAssemblyFile(b.path("src/prog.s"));


    // This creates another `std.Build.Step.Compile`, but this one builds an executable
    // rather than a static library.
    const exe = b.addExecutable(.{
        .name = "code",
        .root_module = exe_mod,
    });

    exe.setLinkerScript(.{
        .cwd_relative = "linker.ld"
    });


    const oc = exe.addObjCopy(.{
        .format = .bin,
    });


    

    // This declares intent for the executable to be installed into the
    // standard location when the user invokes the "install" step (the default
    // step when running `zig build`).
    b.installArtifact(exe);


    oc.step.dependOn(&exe.step);


    const cp_bin = b.addInstallBinFile(oc.getOutput(), "code.bin");

    b.default_step.dependOn(&cp_bin.step);
}
