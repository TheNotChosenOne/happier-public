{
    description = "Rust stable with WASM and rust-analyzer";

    inputs = {
        nixpkgs.url = "nixpkgs/nixos-unstable";
        flake-utils.url = "github:numtide/flake-utils";
        fenix = {
            url = "github:nix-community/fenix";
            inputs.nixpkgs.follows = "nixpkgs";
        };
    };

    outputs = { self, nixpkgs, fenix, flake-utils }: 
        flake-utils.lib.eachDefaultSystem (system:
        let
            pkgs = import nixpkgs {
                inherit system;
                config.allowUnfree = true;
                overlays = [ fenix.overlays.default ];
            };

            rustToolchain = with fenix.packages.${system}; combine [
                stable.cargo
                stable.clippy
                stable.rustfmt
                stable.rustc
                stable.rust-src
                stable.rust-analyzer
            ];

            customRustPlatform = pkgs.makeRustPlatform {
                cargo = rustToolchain;
                rustc = rustToolchain;
            };

        in
        {
            devShells.default = pkgs.mkShell {
                nativeBuildInputs = with pkgs; [
                ];

                buildInputs = with pkgs; [
                    rustToolchain
                    pkg-config
                    gobject-introspection
                    cargo-tauri
                    cargo-watch
                    cargo-tarpaulin
                    cargo-fuzz
                    cargo-flamegraph
                    gnuplot
                    clang
                    linuxPackages_latest.perf
                    llvmPackages.libclang
                ];

                LD_LIBRARY_PATH = with pkgs; lib.makeLibraryPath [
                    stdenv.cc.cc.lib
                ];

                debug = rustToolchain;

                LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
                RUST_SRC_PATH = "${rustToolchain}/lib/rustlib/src/rust/library";
                RUST_LOG="debug";

                shellHook = ''
                '';

            };
        }
    );
}
