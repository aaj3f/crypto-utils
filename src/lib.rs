use base64;
use bitcoin::consensus::{encode, Encodable};
use bitcoin::hashes::{sha256d, Hash, HashEngine};
use chrono::{DateTime, Datelike, Timelike, Utc};
use hex::FromHex;
use ripemd160::{Digest, Ripemd160};
use secp256k1::bitcoin_hashes::sha256;
use secp256k1::key::PublicKey;
use secp256k1::rand::rngs::OsRng;
use secp256k1::{Message, Secp256k1, SecretKey};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use sha2::Sha256;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::{env, fmt, str};
use unicode_normalization::UnicodeNormalization;
use url::Url;

pub const BITCOIN_SIGNED_MSG_PREFIX: &[u8] = b"\x18Bitcoin Signed Message:\n";

#[derive(Debug, Serialize, Deserialize)]
pub struct HttpRequest {
    pub method: String,
    pub headers: Value,
    pub body: String,
}

impl fmt::Display for HttpRequest {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).unwrap())
    }
}

impl HttpRequest {
    pub fn headers(&self) -> Map<String, Value> {
        let mut map = Map::new();
        for (key, value) in self.headers.as_object().unwrap() {
            map.insert(
                key.to_string(),
                serde_json::to_value(value).unwrap_or(Value::default()),
            )
            .unwrap_or(Value::default());
        }
        map
    }
}

#[derive(Serialize, Deserialize, Debug)]
struct Command {
    r#type: String,
    db: String,
    tx: Value,
    auth: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    fuel: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    nonce: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    expire: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    deps: Option<Vec<i32>>,
}

impl Command {
    fn stringify(&mut self) -> String {
        self.to_string()
    }

    fn sign(&mut self, private_key: &str) -> CommandResult {
        let stringified_command = self.stringify();
        let byte_command: &[u8] = stringified_command.as_bytes();
        let secp = Secp256k1::new();
        let sha_hash = Message::from_hashed_data::<sha256::Hash>(byte_command);
        let private_key = SecretKey::from_slice(&hex::decode(private_key).unwrap())
            .expect("32 bytes, within curve order");
        let recov_sig = secp.sign_recoverable(&sha_hash, &private_key);
        let signature = secp.sign(&sha_hash, &private_key).serialize_der();
        let (recovery_id, _sig_bytes) = recov_sig.serialize_compact();
        let recovery_int = recovery_id.to_i32();
        let additive_int = 27;
        let recovery_byte = hex::encode(&[u8::try_from(additive_int + recovery_int).unwrap()]);
        let mut sig_string = (recovery_byte).to_string();
        sig_string.push_str(&hex::encode(signature.to_vec()));

        CommandResult {
            cmd: stringified_command,
            sig: sig_string,
        }
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).unwrap())
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub struct CommandResult {
    pub cmd: String,
    pub sig: String,
}

impl fmt::Display for CommandResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).unwrap())
    }
}

fn get_rfc1132_date_time(specific_time: Option<String>) -> String {
    let now = match specific_time {
        Some(string_time) => DateTime::parse_from_rfc2822(&string_time)
            .expect("Could not parse DateTime")
            .with_timezone(&Utc),
        None => Utc::now(),
    };
    let weekday = now.weekday();
    let day = now.format("%d");
    let month = now.format("%b");
    let (_is_common_era, year) = now.year_ce();
    let hours = now.hour();
    let minutes = now.minute();
    let seconds = now.second();
    let result = format!(
        "{}, {} {} {} {}:{}:{} GMT",
        weekday, day, month, year, hours, minutes, seconds
    );
    result
}

pub fn normalize_string(string: &str) -> String {
    string.nfc().collect::<String>()
}

pub fn string_to_byte_array(string: &str) -> Vec<u8> {
    normalize_string(string).as_bytes().to_vec()
}

// pub fn base_ty_byte_array<T>(base_val: impl ToBytes) -> Vec<u8> {}

pub fn generate_key_pair() -> HashMap<String, String> {
    let secp = Secp256k1::new();
    let mut rng = OsRng::new().expect("OsRng");
    let (private_key, public_key) = secp.generate_keypair(&mut rng);
    let mut result = HashMap::new();
    result.insert(String::from("privateKey"), private_key.to_string());
    result.insert(String::from("publicKey"), public_key.to_string());
    result
}

//take pubkey hex -> pubkey struct -> get prefix & checksum, where prefix is pubkey sha256->ripemd160 concat 15, 2 and where checksum is first 4 bytes of the prefix dub sha hashed. then concat prefix and checksum
pub fn get_sin_from_public_key(x: &str) -> String {
    //hex string -> byte array
    let mut addrv: Vec<u8> = Vec::with_capacity(65);
    addrv.append(&mut <Vec<u8>>::from_hex(x).unwrap());

    //byte array -> PublicKey
    addrv = PublicKey::from_slice(&addrv).unwrap().serialize().to_vec();

    //SHA256 & Ripemd160
    let mut hasher = Sha256::new();
    hasher.update(addrv);
    let sha_digest = hasher.finalize();
    let mut ripemd_digest = Ripemd160::digest(&sha_digest.as_ref()).as_slice().to_vec();

    //Arbitrarily insert 0x0F 0x02
    ripemd_digest.insert(0, 15);
    ripemd_digest.insert(1, 2);

    //Construct checksum w/ double-SHA256 of ripemd_digest
    hasher = Sha256::new();
    hasher.update(&ripemd_digest);
    let c1 = hasher.finalize();
    hasher = Sha256::new();
    hasher.update(&c1);
    let checksum = hasher.finalize();

    //Concat ripemd_digest with checksum
    ripemd_digest.extend_from_slice(&checksum[..4]);

    //Base58 Encode against Bitcoin Alphabet
    bs58::encode(&ripemd_digest)
        .with_alphabet(bs58::Alphabet::BITCOIN)
        .into_string()
}

pub fn sign_transaction(
    auth: &str,
    db: &str,
    expire: Option<u64>,
    fuel: Option<i32>,
    nonce: Option<i32>,
    private_key: &str,
    tx: &str,
    deps: Option<Vec<i32>>,
) -> CommandResult {
    let db: String = String::from(db).to_lowercase();
    let tx = serde_json::from_str(tx).unwrap_or(Value::default());
    let mut cmd = Command {
        r#type: String::from("tx"),
        db: db,
        tx: tx,
        auth: String::from(auth),
        fuel,
        nonce,
        expire,
        deps,
    };
    cmd.sign(private_key)
}
pub fn sign_query(
    private_key: &str,
    param: &str,
    query_type: &str,
    host: &str,
    db: &str,
    auth: Option<String>,
) -> HttpRequest {
    let _unused_host = host;
    let db: String = String::from(db).to_lowercase();

    let test_time = match env::var("TEST_ENV_VAR_TIME") {
        Ok(v) => Some(v),
        Err(_) => None,
    };
    let formatted_date = get_rfc1132_date_time(test_time);
    let byte_command: &[u8] = param.as_bytes();
    let mut hasher = Sha256::new();
    hasher.update(byte_command);
    let sha_digest = hasher.finalize();
    let digest = base64::encode(&sha_digest);
    let uri = format!("/fdb/{}/{}", db, query_type.to_lowercase());
    let signing_string = format!(
        "(request-target): post {}\nx-fluree-date: {}\ndigest: SHA-256={}",
        uri, formatted_date, digest
    );
    let byte_command: &[u8] = signing_string.as_bytes();
    let secp = Secp256k1::new();
    let sha_hash = Message::from_hashed_data::<sha256::Hash>(byte_command);
    let private_key = SecretKey::from_slice(&hex::decode(private_key).unwrap())
        .expect("32 bytes, within curve order");
    let recov_sig = secp.sign_recoverable(&sha_hash, &private_key);
    let der_sig = secp.sign(&sha_hash, &private_key).serialize_der();
    let (recovery_id, _sig_bytes) = recov_sig.serialize_compact();
    let recovery_int = recovery_id.to_i32();
    let additive_int = 27;
    let recovery_byte = hex::encode(&[u8::try_from(additive_int + recovery_int).unwrap()]);
    let mut sig_string = (recovery_byte).to_string();
    sig_string.push_str(&hex::encode(der_sig.to_vec()));
    let auth_str = match auth {
        Some(str_val) => str_val,
        None => String::from("na"),
    };

    let signature = format!("keyId=\\\"{}\\\",headers=\\\"(request-target) x-fluree-date digest\\\",algorithm=\\\"ecdsa-sha256\\\",signature=\\\"{}\\\"", auth_str, sig_string);

    let header_string = format!(
        r#"
        {{
            "Content-Type": "appication/json",
            "X-Fluree-Date": "{}",
            "Digest": "SHA-256={}",
            "Signature": "{}"
        }}"#,
        formatted_date, digest, signature
    );
    let headers = serde_json::from_str(&header_string).expect("Could not serialize into JSON");

    HttpRequest {
        method: String::from("POST"),
        headers,
        body: String::from(param),
    }
}
pub fn sign_request(
    method: &str,
    url: &str,
    body: &str,
    private_key: &str,
    auth: Option<String>,
) -> HttpRequest {
    let uri_parts = Url::parse(url).expect("URL string was malformed");
    println!("The path part of the URL is: {}", uri_parts.path());
    let test_time = match env::var("TEST_ENV_VAR_TIME") {
        Ok(v) => Some(v),
        Err(_) => None,
    };
    let formatted_date = get_rfc1132_date_time(test_time);
    println!("formatted_date: {:?}", formatted_date);

    let byte_command: &[u8] = body.as_bytes();
    let mut hasher = Sha256::new();
    hasher.update(byte_command);
    let sha_digest = hasher.finalize();
    let digest = base64::encode(&sha_digest);

    let signing_string = format!(
        "(request-target): post {}\nx-fluree-date: {}\ndigest: SHA-256={:?}",
        uri_parts.path(),
        formatted_date,
        digest
    );
    let byte_command: &[u8] = signing_string.as_bytes();
    let secp = Secp256k1::new();
    let sha_hash = Message::from_hashed_data::<sha256::Hash>(byte_command);
    let private_key = SecretKey::from_slice(&hex::decode(private_key).unwrap())
        .expect("32 bytes, within curve order");
    let recov_sig = secp.sign_recoverable(&sha_hash, &private_key);
    let der_sig = secp.sign(&sha_hash, &private_key).serialize_der();
    let (recovery_id, _sig_bytes) = recov_sig.serialize_compact();
    let recovery_int = recovery_id.to_i32();
    let additive_int = 27;
    let recovery_byte = hex::encode(&[u8::try_from(additive_int + recovery_int).unwrap()]);
    let mut sig_string = (recovery_byte).to_string();
    sig_string.push_str(&hex::encode(der_sig.to_vec()));
    let auth_str = match auth {
        Some(str_val) => str_val,
        None => String::from("na"),
    };

    let signature = format!("keyId=\\\"{}\\\",headers=\\\"(request-target) x-fluree-date digest\\\",algorithm=\\\"ecdsa-sha256\\\",signature=\\\"{}\\\"", auth_str, sig_string);

    let headers: Value = serde_json::from_str(&format!(
        r#"
        {{
            "Content-Type": "appication/json",
            "X-Fluree-Date": "{}",
            "Digest": "SHA-256={}",
            "Signature": "{}"
        }}"#,
        formatted_date, digest, signature
    ))
    .expect("Could not serialize into JSON");
    HttpRequest {
        method: String::from(method),
        headers,
        body: String::from(body),
    }
}

pub fn signed_msg_hash(msg: &str) -> sha256d::Hash {
    let mut engine = sha256d::Hash::engine();
    engine.input(BITCOIN_SIGNED_MSG_PREFIX);
    let msg_len = encode::VarInt(msg.len() as u64);
    msg_len.consensus_encode(&mut engine).unwrap();
    engine.input(msg.as_bytes());
    sha256d::Hash::from_engine(engine)
}

#[cfg(test)]
mod tests {
    use super::*;
    use secp256k1::bitcoin_hashes::sha256;
    use secp256k1::Message;

    #[test]
    fn can_normalize_string() {
        let s = "ÅΩ";
        let c = normalize_string(s);
        assert_eq!(c, "ÅΩ");
    }

    #[test]
    fn can_generate_key_pair() {
        let secp = Secp256k1::new();
        let keypair = generate_key_pair();
        let private_key_string = keypair.get("privateKey").unwrap();
        let message = Message::from_hashed_data::<sha256::Hash>("Hello World!".as_bytes());
        let secret_key =
            SecretKey::from_slice(&hex::decode(private_key_string.as_bytes()).unwrap()).unwrap();
        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
        let sig = secp.sign(&message, &secret_key);
        println!("Secret Key: {:?}", secret_key);
        assert!(secp.verify(&message, &sig, &public_key).is_ok());
    }

    #[test]
    fn can_derive_auth_id_from_pub_key() {
        let pub_key_1 = "02a36b64f18a358037ef8639838e269279271e988dca880bda67bcbd0aad26617a";
        let auth_id_1 = "Tf6UGQrRiMbzuZm5yLZaZrA5AEs5gPitXaX";
        let pub_key_2 = "0357b3f30f8874ef958f9347dcf6448273ff93a809aaf238aa40404e5039f9badc";
        let auth_id_2 = "TfCJVvboFq5iMr2aa8Be4LiG2akhXTToNux";
        assert_eq!(get_sin_from_public_key(&pub_key_1), auth_id_1);
        assert_eq!(get_sin_from_public_key(&pub_key_2), auth_id_2);
    }

    #[test]
    fn can_serialize() {
        let command = Command {
            r#type: String::from("tx"),
            db: String::from("ledger/test"),
            tx: serde_json::from_str(
                r#"
        {
            "_id": "_user",
            "username": "andrew"
        }"#,
            )
            .unwrap(),
            auth: String::from("auth"),
            fuel: None,
            nonce: None,
            expire: None,
            deps: None,
        };
        println!("{}", command)
    }

    #[test]
    fn can_gen_command() {
        let expected_value1 = CommandResult {
            cmd:String::from("{\"type\":\"tx\",\"db\":\"asu/test1\",\"tx\":[{\"_id\":\"_user\",\"username\":\"pleaseWork\"}],\"auth\":\"TfHjMEUskWg3EqvLetEwUxNQ9rjE46hRy74\",\"fuel\":1000000,\"nonce\":27,\"expire\":1620330340609}"
),
            sig: String::from("1c3044022018889e7dfb3fb4407c028dafaa7257b51e047b1acb8fcbd678b175260d567fe702205a93998b16124f40d7a32d8fd576fc4bff57ed018e38cba247d1ff8721584515")
        };
        let expected_value2 = CommandResult {
            cmd:String::from("{\"type\":\"tx\",\"db\":\"asu/test1\",\"tx\":[{\"_id\":\"_user\",\"username\":\"pleaseWork1\"}],\"auth\":\"Tf2LGtCR5dSVXpKTnAF5E5s6LWiM1Mj1bCV\",\"fuel\":1000000,\"nonce\":2,\"expire\":1620330628141}"
),
            sig: String::from("1b3045022100ff70b52f343bb4ef49e90fdb1d34574f3e1a56bd6619a5ca5c5b5a04d45c080d0220042cfe8b1c76b513b3127b4a1d3a3b9d8e8b35edbbc4d28878b77fc8925ece9f")
        };
        let expected_value3 = CommandResult {
            cmd:String::from("{\"type\":\"tx\",\"db\":\"asu/test1\",\"tx\":[{\"_id\":\"_user\",\"username\":\"pleaseWork2\"}],\"auth\":\"TexHuicPSD6R96aQXtEEEvd5KLjyMAtztNi\",\"fuel\":1000000,\"nonce\":19,\"expire\":1620330748598}"
),
            sig: String::from("1b3044022074bf295d4d36ddf4191b5404b3835e0939b7d415f777365eb846fef96c242a6202206ca7345d5f50684195249cb5972bd2a4195e23c0f6ecc578f04404a44ee11f6d")
        };
        let auth1 = "TfHjMEUskWg3EqvLetEwUxNQ9rjE46hRy74";
        let auth2 = "Tf2LGtCR5dSVXpKTnAF5E5s6LWiM1Mj1bCV";
        let auth3 = "TexHuicPSD6R96aQXtEEEvd5KLjyMAtztNi";
        let db = "asu/test1";
        let expire1: u64 = 1620330340609;
        let expire2: u64 = 1620330628141;
        let expire3: u64 = 1620330748598;
        let fuel: i32 = 1000000;
        let nonce1: i32 = 27;
        let nonce2: i32 = 2;
        let nonce3: i32 = 19;
        let private_key1 = "1923dabf084da2210ecd5098424891896b66c429770ce25654bd95206c101328";
        let private_key2 = "df89faece99f12414fbc0c596f961f91ac6c65a960c246802358349e41c9000f";
        let private_key3 = "231b648946f4da4a55ab824b1cfa39c320fc459be107aaa6cf70669fdfa0350c";
        let tx1 = "[{\"_id\":\"_user\",\"username\":\"pleaseWork\"}]";
        let tx2 = "[{\"_id\":\"_user\",\"username\":\"pleaseWork1\"}]";
        let tx3 = "[{\"_id\":\"_user\",\"username\":\"pleaseWork2\"}]";
        let signed_transaction1 = sign_transaction(
            auth1,
            db,
            Some(expire1),
            Some(fuel),
            Some(nonce1),
            private_key1,
            tx1,
            None,
        );
        let signed_transaction2 = sign_transaction(
            auth2,
            db,
            Some(expire2),
            Some(fuel),
            Some(nonce2),
            private_key2,
            tx2,
            None,
        );
        let signed_transaction3 = sign_transaction(
            auth3,
            db,
            Some(expire3),
            Some(fuel),
            Some(nonce3),
            private_key3,
            tx3,
            None,
        );
        assert_eq!(signed_transaction1.cmd, expected_value1.cmd);
        assert_eq!(signed_transaction2.cmd, expected_value2.cmd);
        assert_eq!(signed_transaction3.cmd, expected_value3.cmd);
    }

    #[test]
    fn can_gen_sig() {
        let expected_value1 = CommandResult {
            cmd:String::from("{\"type\":\"tx\",\"db\":\"asu/test1\",\"tx\":[{\"_id\":\"_user\",\"username\":\"pleaseWork\"}],\"auth\":\"TfHjMEUskWg3EqvLetEwUxNQ9rjE46hRy74\",\"fuel\":1000000,\"nonce\":27,\"expire\":1620330340609}"
),
            sig: String::from("1c3044022018889e7dfb3fb4407c028dafaa7257b51e047b1acb8fcbd678b175260d567fe702205a93998b16124f40d7a32d8fd576fc4bff57ed018e38cba247d1ff8721584515")
        };
        let expected_value2 = CommandResult {
            cmd:String::from("{\"type\":\"tx\",\"db\":\"asu/test1\",\"tx\":[{\"_id\":\"_user\",\"username\":\"pleaseWork1\"}],\"auth\":\"Tf2LGtCR5dSVXpKTnAF5E5s6LWiM1Mj1bCV\",\"fuel\":1000000,\"nonce\":2,\"expire\":1620330628141}"
),
            sig: String::from("1b3045022100ff70b52f343bb4ef49e90fdb1d34574f3e1a56bd6619a5ca5c5b5a04d45c080d0220042cfe8b1c76b513b3127b4a1d3a3b9d8e8b35edbbc4d28878b77fc8925ece9f")
        };
        let expected_value3 = CommandResult {
            cmd:String::from("{\"type\":\"tx\",\"db\":\"asu/test1\",\"tx\":[{\"_id\":\"_user\",\"username\":\"pleaseWork2\"}],\"auth\":\"TexHuicPSD6R96aQXtEEEvd5KLjyMAtztNi\",\"fuel\":1000000,\"nonce\":19,\"expire\":1620330748598}"
),
            sig: String::from("1b3044022074bf295d4d36ddf4191b5404b3835e0939b7d415f777365eb846fef96c242a6202206ca7345d5f50684195249cb5972bd2a4195e23c0f6ecc578f04404a44ee11f6d")
        };
        let auth1 = "TfHjMEUskWg3EqvLetEwUxNQ9rjE46hRy74";
        let auth2 = "Tf2LGtCR5dSVXpKTnAF5E5s6LWiM1Mj1bCV";
        let auth3 = "TexHuicPSD6R96aQXtEEEvd5KLjyMAtztNi";
        let db = "asu/test1";
        let expire1: u64 = 1620330340609;
        let expire2: u64 = 1620330628141;
        let expire3: u64 = 1620330748598;
        let fuel: i32 = 1000000;
        let nonce1: i32 = 27;
        let nonce2: i32 = 2;
        let nonce3: i32 = 19;
        let private_key1 = "1923dabf084da2210ecd5098424891896b66c429770ce25654bd95206c101328";
        let private_key2 = "df89faece99f12414fbc0c596f961f91ac6c65a960c246802358349e41c9000f";
        let private_key3 = "231b648946f4da4a55ab824b1cfa39c320fc459be107aaa6cf70669fdfa0350c";
        let tx1 = "[{\"_id\":\"_user\",\"username\":\"pleaseWork\"}]";
        let tx2 = "[{\"_id\":\"_user\",\"username\":\"pleaseWork1\"}]";
        let tx3 = "[{\"_id\":\"_user\",\"username\":\"pleaseWork2\"}]";
        let signed_transaction1 = sign_transaction(
            auth1,
            db,
            Some(expire1),
            Some(fuel),
            Some(nonce1),
            private_key1,
            tx1,
            None,
        );
        assert_eq!(signed_transaction1.sig, expected_value1.sig);
        let signed_transaction2 = sign_transaction(
            auth2,
            db,
            Some(expire2),
            Some(fuel),
            Some(nonce2),
            private_key2,
            tx2,
            None,
        );
        assert_eq!(signed_transaction2.sig, expected_value2.sig);
        let signed_transaction3 = sign_transaction(
            auth3,
            db,
            Some(expire3),
            Some(fuel),
            Some(nonce3),
            private_key3,
            tx3,
            None,
        );
        assert_eq!(signed_transaction3.sig, expected_value3.sig);
    }

    #[test]
    fn can_sign_query() {
        let string_headers = r#"
        {
            "Content-Type": "appication/json",
            "X-Fluree-Date": "Sun, 09 May 2021 13:25:49 GMT",
            "Digest": "SHA-256=tqhS85d05mvYlGgSR6VE6W09gCOt8tb4sWOcypKp8PM=",
            "Signature": "keyId=\"na\",headers=\"(request-target) x-fluree-date digest\",algorithm=\"ecdsa-sha256\",signature=\"1c304402207b7180f3dc530be6fe77dcfd5f7254f6ae37a461000b9878a54845e3ba41a18a02206abb3ab24ec85656a271faa2e951296a55aa63810920a205f87d18f6c3c8bf5a\""

        }"#;
        env::set_var("TEST_ENV_VAR_TIME", "Sun, 09 May 2021 13:25:49 GMT");
        let headers = serde_json::from_str(string_headers).expect("Could not serialize into JSON");
        let expected_request = HttpRequest {
            method: String::from("POST"),
            body: String::from(
                "{\"select\":[\"*\",{\"roles\":[\"*\",{\"rules\":[\"*\"]}]}],\"from\":\"_user\"}",
            ),
            headers: headers,
        };
        let private_key = "73d410544cbaf19810c2fab90dfb427227e3efd5ad3b4c12b7abf1f361667947";
        let param =
            "{\"select\":[\"*\",{\"roles\":[\"*\",{\"rules\":[\"*\"]}]}],\"from\":\"_user\"}";
        let query_type = "query";
        let host = "localhost";
        let db = "asu/test1";
        // let auth = Some(String::from("Tf33mCxFory8fWb55DkGv3nZ4ytCsy11fjW"));
        let auth = None;
        let signed_request = sign_query(private_key, param, query_type, host, db, auth);
        println!("EXPECTED_REQUEST = {:?}", signed_request.headers);
        assert_eq!(signed_request.body, expected_request.body);
        assert_eq!(signed_request.method, expected_request.method);
        assert_eq!(signed_request.headers, expected_request.headers);
    }

    #[test]
    fn can_sign_request() {
        // POST /fdb/asu/test1/query HTTP/1.1
        // Host: localhost:8090
        // Connection: keep-alive
        // Content-Length: 63
        // sec-ch-ua: " Not A;Brand";v="99", "Chromium";v="90", "Google Chrome";v="90"
        // X-Fluree-Date: Fri, 07 May 2021 20:54:26 GMT
        // Signature: keyId="na",headers="(request-target) x-fluree-date digest",algorithm="ecdsa-sha256",signature="1b3045022100cbd32e463567fefc2f120425b0224d9d263008911653f50e83953f47cfbef3bc0220565fde78aa03d4311819b743fc8175ef0f77e8b000d16deeefc6e3d426830be7"
        // Digest: SHA-256=CjzQyC4QDKlCFEKihBMCoFTHYnxv0KcbmXVnWsGpZFc=
        // sec-ch-ua-mobile: ?0
        // User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/90.0.4430.93 Safari/537.36
        // Content-Type: application/json
        // Accept: */*
        // Origin: http://localhost:8090
        // Sec-Fetch-Site: same-origin
        // Sec-Fetch-Mode: cors
        // Sec-Fetch-Dest: empty
        // Referer: http://localhost:8090/flureeql
        // Accept-Encoding: gzip, deflate, br
        // Accept-Language: en-US,en;q=0.9
        // Cookie: _ga=GA1.1.954238342.1606845966; intercom-id-d3fog09r=8af0f1b6-23f9-4dea-ac21-ad4e6dff6e6f; _ga_YXJ1XBN2M9=GS1.1.1609790170.6.0.1609790170.0; _ga_REKSDEB65X=GS1.1.1618839302.1.1.1618840767.0
        let string_headers = r#"
        {
            "Content-Type": "appication/json",
            "X-Fluree-Date": "Sun, 09 May 2021 13:25:49 GMT",
            "Digest": "SHA-256=tqhS85d05mvYlGgSR6VE6W09gCOt8tb4sWOcypKp8PM=",
            "Signature": "keyId=\"na\",headers=\"(request-target) x-fluree-date digest\",algorithm=\"ecdsa-sha256\",signature=\"1b304502210096889515c74fad981f9e38907c400a56b7e70d4bfbcddc1723d06ef2190384f702202c93ca84a77da02858fe451ab07cd73cbccd9aedaa3fb25f98f459040503a58c\""
        }"#;
        env::set_var("TEST_ENV_VAR_TIME", "Sun, 09 May 2021 13:25:49 GMT");
        let headers = serde_json::from_str(string_headers).expect("Could not serialize into JSON");
        let expected_request = HttpRequest {
            method: String::from("POST"),
            body: String::from(
                "{\"select\":[\"*\",{\"roles\":[\"*\",{\"rules\":[\"*\"]}]}],\"from\":\"_user\"}",
            ),
            headers: headers,
        };
        let private_key = "73d410544cbaf19810c2fab90dfb427227e3efd5ad3b4c12b7abf1f361667947";
        let body =
            "{\"select\":[\"*\",{\"roles\":[\"*\",{\"rules\":[\"*\"]}]}],\"from\":\"_user\"}";
        let auth = None;
        let url = "http://localhost:8090/fdb/asu/test1/query";
        let method = "POST";
        let signed_request = sign_request(method, url, body, private_key, auth);
        println!("SIGNED_REQUEST = {:?}", signed_request);
        println!("EXPECTED_REQUEST = {:?}", expected_request);
        assert_eq!(signed_request.body, expected_request.body);
        assert_eq!(signed_request.method, expected_request.method);
        assert_eq!(signed_request.headers, expected_request.headers);
    }
}
