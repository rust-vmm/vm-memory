fn main() {
    // Define a `xen` attribute, which is used for conditional
    // compilation of "xen".
    println!("cargo:rustc-check-cfg=cfg(xen)");
    // `xen` would be enabled with `XEN=ENABLE`
    if let Ok(xen) = std::env::var("XEN") {
        match xen.as_str() {
            "ENABLE" => {
                println!("cargo:rustc-cfg=xen");
            }
            _ => {
                eprintln!("XEN environment variable is provided but not enabled, if you want to compile with XEN please use `XEN=ENABLE`");
            }
        }
    }
}
