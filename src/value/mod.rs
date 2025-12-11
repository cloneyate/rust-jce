use crate::de::{read_header, read_len};
use crate::error::{DecodeError, DecodeResult};
use crate::types;
use bytes::{Buf, Bytes};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

#[derive(Debug)]
pub enum Value {
    Byte(i8),
    Short(i16),
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    Bytes(Bytes),
    Struct(HashMap<u8, Value>),
    Map(HashMap<Value, Value>),
    List(Vec<Value>),
    Empty,
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Byte(a), Value::Byte(b)) => a == b,
            (Value::Short(a), Value::Short(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Long(a), Value::Long(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Double(a), Value::Double(b)) => a == b,
            (Value::Bytes(a), Value::Bytes(b)) => a == b,
            (Value::Struct(a), Value::Struct(b)) => a == b,
            (Value::Map(a), Value::Map(b)) => a == b,
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Empty, Value::Empty) => true,
            _ => false,
        }
    }
}

impl Eq for Value {}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Byte(b) => b.hash(state),
            Value::Short(s) => s.hash(state),
            Value::Int(i) => i.hash(state),
            Value::Long(l) => l.hash(state),
            Value::Float(f) => {
                state.write_u8(b'f');
                state.write_u32(f.to_bits());
            }
            Value::Double(d) => {
                state.write_u8(b'd');
                state.write_u64(d.to_bits());
            }
            Value::Bytes(b) => b.hash(state),
            Value::Struct(s) => {
                state.write_usize(s.len());
                state.write_u8(b's');

                for (k, v) in s.iter() {
                    state.write_u8(*k);
                    v.hash(state);
                }
            }
            Value::Map(m) => {
                state.write_usize(m.len());
                state.write_u8(b'm');

                for (k, v) in m.iter() {
                    k.hash(state);
                    v.hash(state);
                }
            }
            Value::List(v) => {
                for val in v {
                    val.hash(state);
                }
            }
            Value::Empty => state.write(b"empty"),
        }
    }
}

fn read_value<B: Buf>(buf: &mut B, t: u8) -> DecodeResult<Value> {
    fn bytes_from_buf<B: Buf>(buf: &mut B, len: usize) -> Bytes {
        if len > 0 {
            buf.copy_to_bytes(len)
        } else {
            Bytes::new()
        }
    }

    let val = match t {
        types::BYTE => Value::Byte(buf.get_i8()),
        types::SHORT => Value::Short(buf.get_i16()),
        types::INT => Value::Int(buf.get_i32()),
        types::LONG => Value::Long(buf.get_i64()),
        types::FLOAT => Value::Float(buf.get_f32()),
        types::DOUBLE => Value::Double(buf.get_f64()),
        types::SHORT_BYTES => Value::Bytes({
            let len = buf.get_u8() as usize;

            bytes_from_buf(buf, len)
        }),
        types::LONG_BYTES => Value::Bytes({
            let len = buf.get_u32() as usize;

            bytes_from_buf(buf, len)
        }),
        types::STRUCT_START => Value::Struct({
            let mut struct_map = HashMap::new();

            loop {
                if buf.remaining() == 0 {
                    return Err(DecodeError::Eof);
                }

                let header = read_header(buf)?;

                if header.value_type() == types::STRUCT_END {
                    break;
                }

                let field_value = read_value(buf, header.value_type())?;

                struct_map.insert(header.tag(), field_value);
            }

            struct_map
        }),
        types::STRUCT_END => return Err(DecodeError::InvalidType),
        types::MAP => Value::Map({
            let len = read_len(buf)?;

            let mut map = HashMap::<Value, Value>::new();

            for _ in 0..len {
                let key = read_elem(buf)?;
                let value = read_elem(buf)?;
                map.insert(key, value);
            }

            map
        }),
        types::LIST => Value::List({
            let len = read_len(buf)?;

            let mut list = Vec::with_capacity(len);

            for _ in 0..len {
                list.push(read_elem(buf)?);
            }

            list
        }),
        types::EMPTY => Value::Empty,
        types::SINGLE_LIST => Value::Bytes({
            let elem_type = buf.get_u8();

            if elem_type != types::BYTE {
                return Err(DecodeError::InvalidType);
            }

            let len = read_len(buf)?;

            bytes_from_buf(buf, len)
        }),
        _ => return Err(DecodeError::InvalidType),
    };

    Ok(val)
}

pub fn read_elem<B: Buf>(buf: &mut B) -> DecodeResult<Value> {
    let t = buf.get_u8() & 0xF;
    read_value(buf, t)
}

pub fn read_to_hashmap<B: Buf>(mut buf: B) -> DecodeResult<HashMap<u8, Value>> {
    let mut map = HashMap::new();

    while buf.remaining() > 0 {
        let header = read_header(&mut buf)?;
        let value = read_value(&mut buf, header.value_type())?;

        map.insert(header.tag(), value);
    }

    Ok(map)
}

#[cfg(test)]
mod tests {
    use crate::value::read_to_hashmap;

    #[test]
    fn de() {
        let bytes: &[u8] = &[
            25, 0, 5, 0, 1, 0, 2, 6, 6, 232, 182, 133, 229, 184, 130, 6, 6, 49, 49, 52, 53, 49, 52,
            2, 0, 29, 75, 66, 40, 0, 2, 6, 1, 49, 18, 0, 1, 191, 82, 6, 4, 49, 57, 49, 57, 17, 3,
            42,
        ];

        let s = read_to_hashmap(bytes);

        assert!(s.is_ok());
    }

    #[test]
    fn de2() {
        let bytes = [0, 127, 24, 12];

        assert!(read_to_hashmap(bytes.as_ref()).is_ok());
    }

    #[test]
    fn de_vec_struct_with_single_list() {
        let bytes = hex::decode("0900050a030000019a43157fbf1268fe5f96200a300f400f5d00001ed13859b4ec0dbaef8e62a88d57a6aa8aa4f2006b29e8bb2807b78e40dc8c0b0a030000019a4ca4ca19126906eef9200a300740075d00000effec910b219130fc9210558764410b0a030000019a59e5cbd4126909617b200a300340035d0000068b88a92a89a80b0a030000019a5e95544212690cc617200a300140015d00000288880b0a030000019a5e95544212690df92c200a300140015d000002cf390b").unwrap();
        assert!(read_to_hashmap(bytes.as_ref()).is_ok());
    }

    #[test]
    fn de_struct_with_map(){
        let bytes = hex::decode("08000a0c16804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a303a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a303a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a303a2d31000116804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a313a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a313a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a313a2d31000216804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a323a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a323a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a323a2d31000316804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a333a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a333a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a333a2d31000416804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a343a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a343a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a343a2d31000516804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a353a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a353a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a353a2d31000616804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a363a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a363a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a363a2d31000716804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a373a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a373a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a373a2d31000816804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a383a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a383a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a383a2d31000916804443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572313a393a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572333a393a2d312c4443616368653a5a6879446576546573745f677a745f4d4b564361636865536572766572323a393a2d311001").unwrap();
        assert!(read_to_hashmap(bytes.as_ref()).is_ok());
    }

    #[test]
    fn zerocopy_to_bytes(){
        let source: bytes::Bytes = bytes::Bytes::from_static(&[
            25, 0, 5, 0, 1, 0, 2, 6, 6, 232, 182, 133, 229, 184, 130, 6, 6, 49, 49, 52, 53, 49, 52,
            2, 0, 29, 75, 66, 40, 0, 2, 6, 1, 49, 18, 0, 1, 191, 82, 6, 4, 49, 57, 49, 57, 17, 3,
            42,
        ]);
        let source_ptr = source.as_ptr() as usize;
        let s = read_to_hashmap(source);
        assert!(s.is_ok());
        if let crate::value::Value::List(values ) = s.unwrap().get(&1).unwrap() {
            if let crate::value::Value::Bytes(b) = &values[3] {
                assert_eq!(b.as_ref(), b"114514");
                // assert whether b is zero copy from source
                assert!(!b.is_unique());
                let b_ptr = b.as_ptr() as usize;
                assert_eq!(source_ptr + 17, b_ptr);
            } else {
                panic!("Expected Bytes value");
            }
        } else {
            panic!("Expected List value");
        }
    }
}
