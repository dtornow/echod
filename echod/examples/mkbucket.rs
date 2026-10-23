//! Create a bucket on an S3 API: `cargo run -p echod --example mkbucket -- <bucket> <endpoint> [region]`.
//! Credentials come from the environment. For emulators that have no bucket yet.

#[tokio::main]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (bucket, endpoint) = (&args[1], &args[2]);
    let region = args.get(3).cloned().unwrap_or_else(|| "us-east-1".to_string());
    let shared = aws_config::defaults(aws_config::BehaviorVersion::latest()).region(aws_config::Region::new(region)).endpoint_url(endpoint).load().await;
    let client = aws_sdk_s3::Client::from_conf(aws_sdk_s3::config::Builder::from(&shared).force_path_style(true).build());
    match client.create_bucket().bucket(bucket).send().await {
        Ok(_) => println!("created {bucket}"),
        Err(e) => {
            let already = e.as_service_error().map(|s| s.is_bucket_already_owned_by_you() || s.is_bucket_already_exists()).unwrap_or(false);
            if already { println!("{bucket} exists") } else { eprintln!("{e:?}"); std::process::exit(1) }
        }
    }
}
