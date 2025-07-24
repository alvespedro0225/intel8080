pub use intel8080::hardware::Intel8080;
mod intel8080;
pub fn create_cpu() -> Intel8080 {
    Intel8080::default()
}