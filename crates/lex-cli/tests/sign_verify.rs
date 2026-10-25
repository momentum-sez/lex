use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    time::{SystemTime, UNIX_EPOCH},
};

struct SignedFixture {
    directory: PathBuf,
    key: PathBuf,
    bundle: PathBuf,
}

impl SignedFixture {
    fn new(case: &str) -> Self {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            std::env::temp_dir().join(format!("lex-cli-{case}-{}-{stamp}", std::process::id()));
        fs::create_dir(&directory).unwrap();
        let source = directory.join("source.lex");
        let key = directory.join("key.bin");
        let bundle = directory.join("source.signed");
        fs::write(&source, "lambda (ctx : T) . ctx").unwrap();
        fs::write(&key, b"test-signing-key").unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_lex"))
            .arg("sign")
            .arg(&source)
            .arg("--key")
            .arg(&key)
            .arg("--output")
            .arg(&bundle)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        Self {
            directory,
            key,
            bundle,
        }
    }

    fn verify(&self, key: &Path) -> Output {
        Command::new(env!("CARGO_BIN_EXE_lex"))
            .arg("verify")
            .arg(&self.bundle)
            .env("LEX_VERIFY_KEY", key)
            .output()
            .unwrap()
    }

    fn require_valid(&self) {
        let result = self.verify(&self.key);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

impl Drop for SignedFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn sign_then_verify_roundtrips_with_matching_key() {
    let fixture = SignedFixture::new("matching-key");
    fixture.require_valid();
}

#[test]
fn verify_rejects_tampered_source() {
    let fixture = SignedFixture::new("tampered-source");
    fixture.require_valid();
    let mut bundle: serde_json::Value =
        serde_json::from_slice(&fs::read(&fixture.bundle).unwrap()).unwrap();
    bundle["source"] = serde_json::json!("lambda (ctx : T) . Changed");
    fs::write(&fixture.bundle, serde_json::to_vec(&bundle).unwrap()).unwrap();
    let result = fixture.verify(&fixture.key);
    assert!(!result.status.success());
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("content digest mismatch"),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn verify_rejects_wrong_key() {
    let fixture = SignedFixture::new("wrong-key");
    fixture.require_valid();
    let wrong_key = fixture.directory.join("wrong-key.bin");
    fs::write(&wrong_key, b"different-test-key").unwrap();
    let result = fixture.verify(&wrong_key);
    assert!(!result.status.success());
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("authenticator mismatch"),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}
