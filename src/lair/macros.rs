#[macro_export]
macro_rules! func {
    (fn $name:ident($( $in:ident $(: [$in_size:expr])? ),*): [$size:expr] $lair:tt) => {{
        $(let $in = $crate::var!($in $(, $in_size)?);)*
        $crate::lair::expr::FuncE {
            name: $crate::lair::Name(stringify!($name)),
            invertible: false,
            input_params: [$($crate::var!($in $(, $in_size)?)),*].into(),
            output_size: $size,
            body: $crate::block_init!($lair),
        }
    }};
    (invertible fn $name:ident($( $in:ident $(: [$in_size:expr])? ),*): [$size:expr] $lair:tt) => {{
        $(let $in = $crate::var!($in $(, $in_size)?);)*
        $crate::lair::expr::FuncE {
            name: $crate::lair::Name(stringify!($name)),
            invertible: true,
            input_params: [$($crate::var!($in $(, $in_size)?)),*].into(),
            output_size: $size,
            body: $crate::block_init!($lair),
        }
    }};
}

#[macro_export]
macro_rules! var {
    ($variable:ident) => {
        $crate::lair::expr::Var {
            name: stringify!($variable),
            size: 1,
        }
    };
    ($variable:ident, $size:expr) => {
        $crate::lair::expr::Var {
            name: stringify!($variable),
            size: $size,
        }
    };
}

#[macro_export]
macro_rules! block_init {
    ({ $($body:tt)+ }) => {{
        #[allow(unused_mut)]
        let mut ops = vec![];
        $crate::block!({ $($body)+ }, ops)
    }
}}

#[macro_export]
macro_rules! block {
    // Operations
    ({ let $tgt:ident = $a:literal; $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Const($crate::var!($tgt), $crate::lair::field_from_i32($a)));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = [$($a:literal),*]; $($tail:tt)+ }, $ops:expr) => {{
        let arr = vec!($($crate::lair::field_from_i32($a)),*);
        let size = arr.len();
        $ops.push($crate::lair::expr::OpE::Array($crate::var!($tgt, size), arr));
        let $tgt = $crate::var!($tgt, size);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = add($a:ident, $b:ident); $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Add($crate::var!($tgt), $a, $b));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = sub($a:ident, $b:ident); $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Sub($crate::var!($tgt), $a, $b));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = mul($a:ident, $b:ident); $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Mul($crate::var!($tgt), $a, $b));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = div($a:ident, $b:ident); $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Div($crate::var!($tgt), $a, $b));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = inv($a:ident); $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Inv($crate::var!($tgt), $a));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = eq($a:ident, $b:ident); $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Eq($crate::var!($tgt), $a, $b));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = not($a:ident); $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Not($crate::var!($tgt), $a));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = store($($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let inp = [$($arg),*].into();
        $ops.push($crate::lair::expr::OpE::Store($crate::var!($tgt), inp));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let ($($tgt:ident $(: [$size:expr])?),*) = load($arg:ident); $($tail:tt)+ }, $ops:expr) => {{
        let out = [$($crate::var!($tgt $(, $size)?)),*].into();
        $ops.push($crate::lair::expr::OpE::Load(out, $arg));
        $(let $tgt = $crate::var!($tgt $(, $size)?);)*
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let ($($tgt:ident $(: [$size:expr])?),*) = call($func:ident, $($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let func = $crate::lair::Name(stringify!($func));
        let out = [$($crate::var!($tgt $(, $size)?)),*].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::lair::expr::OpE::Call(out, func, inp));
        $(let $tgt = $crate::var!($tgt $(, $size)?);)*
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident $(: [$size:expr])? = call($func:ident, $($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let func = $crate::lair::Name(stringify!($func));
        let out = [$crate::var!($tgt $(, $size)?)].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::lair::expr::OpE::Call(out, func, inp));
        let $tgt = $crate::var!($tgt $(, $size)?);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let ($($tgt:ident $(: [$size:expr])?),*) = preimg($func:ident, $($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let func = $crate::lair::Name(stringify!($func));
        let out = [$($crate::var!($tgt $(, $size)?)),*].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::lair::expr::OpE::PreImg(out, func, inp));
        $(let $tgt = $crate::var!($tgt $(, $size)?);)*
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident $(: [$size:expr])? = preimg($func:ident, $($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let func = $crate::lair::Name(stringify!($func));
        let out = [$crate::var!($tgt $(, $size)?)].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::lair::expr::OpE::PreImg(out, func, inp));
        let $tgt = $crate::var!($tgt $(, $size)?);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ debug!($s:literal); $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Debug($s));
        $crate::block!({ $($tail)* }, $ops)
    }};
    // Pseudo-operations
    ({ let $tgt:ident $(: [$size:expr])? = ($($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let out = [$crate::var!($tgt $(, $size)?)].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::lair::expr::OpE::Slice(out, inp));
        let $tgt = $crate::var!($tgt $(, $size)?);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let ($($tgt:ident $(: [$size:expr])?),*) = ($($arg:ident),*); $($tail:tt)+ }, $ops:expr) => {{
        let out = [$($crate::var!($tgt $(, $size)?)),*].into();
        let inp = [$($arg),*].into();
        $ops.push($crate::lair::expr::OpE::Slice(out, inp));
        $(let $tgt = $crate::var!($tgt $(, $size)?);)*
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let ($($tgt:ident $(: [$size:expr])?),*) = $arg:ident; $($tail:tt)+ }, $ops:expr) => {{
        let out = [$($crate::var!($tgt $(, $size)?)),*].into();
        let inp = [$arg].into();
        $ops.push($crate::lair::expr::OpE::Slice(out, inp));
        $(let $tgt = $crate::var!($tgt $(, $size)?);)*
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = Sym($sym:literal, $mem:ident, $store:ident); $($tail:tt)+ }, $ops:expr) => {{
        let sym = $mem.read_and_ingress($sym, $store).unwrap().raw;
        $ops.push($crate::lair::expr::OpE::Const($crate::var!($tgt), sym));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = $a:ident; $($tail:tt)+ }, $ops:expr) => {{
        let $tgt = $a;
        $crate::block!({ $($tail)* }, $ops)
    }};
    ({ let $tgt:ident = $e:expr; $($tail:tt)+ }, $ops:expr) => {{
        $ops.push($crate::lair::expr::OpE::Const($crate::var!($tgt), $e.to_field()));
        let $tgt = $crate::var!($tgt);
        $crate::block!({ $($tail)* }, $ops)
    }};
    // Control statements
    ({ return ($($src:ident),*) }, $ops:expr) => {{
        let ops = $ops.into();
        let ctrl = $crate::lair::expr::CtrlE::Return([$($src),*].into());
        $crate::lair::expr::BlockE { ops, ctrl }
    }};
    ({ return $src:ident }, $ops:expr) => {{
        let ops = $ops.into();
        let ctrl = $crate::lair::expr::CtrlE::Return([$src].into());
        $crate::lair::expr::BlockE { ops, ctrl }
    }};
    ({ if $x:ident { $($true_block:tt)+ } $($false_block:tt)+ }, $ops:expr) => {{
        let ops = $ops.into();
        let true_block = Box::new($crate::block_init!({ $($true_block)+ }));
        let false_block = Box::new($crate::block_init!({ $($false_block)+ }));
        let ctrl = $crate::lair::expr::CtrlE::If($x, true_block, false_block);
        $crate::lair::expr::BlockE { ops, ctrl }
    }};
    ({ if !$x:ident { $($true_block:tt)+ } $($false_block:tt)+ }, $ops:expr) => {{
        let ops = $ops.into();
        let true_block = Box::new($crate::block_init!({ $($true_block)+ }));
        let false_block = Box::new($crate::block_init!({ $($false_block)+ }));
        let ctrl = $crate::lair::expr::CtrlE::If($x, false_block, true_block);
        $crate::lair::expr::BlockE { ops, ctrl }
    }};
    ({ match $var:ident { $( Tag::$tag:ident $(| Tag::$other_tag:ident)* => $branch:tt )* } $(; $($def:tt)*)? }, $ops:expr) => {{
        let ops = $ops.into();
        let mut vec = Vec::new();
        {
            $(
                vec.push((
                    $crate::lurk::zstore::Tag::$tag.to_field(),
                    $crate::block_init!( $branch )
                ));
                $(
                    vec.push((
                        $crate::lurk::zstore::Tag::$other_tag.to_field(),
                        $crate::block_init!( $branch ),
                    ));
                )*
            )*
        }
        let branches = $crate::lair::map::Map::from_vec(vec);
        let default = None $( .or (Some(Box::new($crate::block_init!({ $($def)* })))) )?;
        let cases = $crate::lair::expr::CasesE { branches, default };
        let ctrl = $crate::lair::expr::CtrlE::Match($var, cases);
        $crate::lair::expr::BlockE { ops, ctrl }
    }};
    ({ match $var:ident { $( $num:literal $(| $other_num:literal)* => $branch:tt )* } $(; $($def:tt)*)? }, $ops:expr) => {{
        let ops = $ops.into();
        let mut vec = Vec::new();
        {
            $(
                vec.push((
                    $crate::lair::field_from_i32($num),
                    $crate::block_init!( $branch )
                ));
                $(
                    vec.push((
                        $crate::lair::field_from_i32($other_num),
                        $crate::block_init!( $branch ),
                    ));
                )*
            )*
        }
        let branches = $crate::lair::map::Map::from_vec(vec);
        let default = None $( .or (Some(Box::new($crate::block_init!({ $($def)* })))) )?;
        let cases = $crate::lair::expr::CasesE { branches, default };
        let ctrl = $crate::lair::expr::CtrlE::Match($var, cases);
        $crate::lair::expr::BlockE { ops, ctrl }
    }};
    ({ match $var:ident { $( $arr:tt $(| $other_arr:tt)* => $branch:tt )* } $(; $($def:tt)*)? }, $ops:expr) => {{
        let ops = $ops.into();
        let mut vec = Vec::new();
        {
            $({
                let arr = $arr.map($crate::lair::field_from_i32).into_iter().collect();
                vec.push((
                    arr,
                    $crate::block_init!( $branch )
                ));
                $({
                    let other_arr = $other_arr.map($crate::lair::field_from_i32).into_iter().collect();
                    vec.push((
                        other_arr,
                        $crate::block_init!( $branch ),
                    ));
                })*
            })*
        }
        let branches = $crate::lair::map::Map::from_vec(vec);
        let default = None $( .or (Some(Box::new($crate::block_init!({ $($def)* })))) )?;
        let cases = $crate::lair::expr::CasesE { branches, default };
        let ctrl = $crate::lair::expr::CtrlE::MatchMany($var, cases);
        $crate::lair::expr::BlockE { ops, ctrl }
    }};
    ({ match_sym($mem:ident, $store:ident) $var:ident { $( $sym:literal $(| $other_sym:literal)* => $branch:tt )* } $(; $($def:tt)*)? }, $ops:expr) => {{
        let ops = $ops.into();
        let mut vec = Vec::new();
        {
            $(
                let sym = $mem.read_and_ingress($sym, $store).unwrap().raw;
                vec.push((
                    sym,
                    $crate::block_init!( $branch )
                ));
                $(
                    let other_sym = $mem.read_and_ingress($other_sym, $store).unwrap().raw;
                    vec.push((
                        other_sym,
                        $crate::block_init!( $branch ),
                    ));
                )*
            )*
        }
        let branches = $crate::lair::map::Map::from_vec(vec);
        let default = None $( .or (Some(Box::new($crate::block_init!({ $($def)* })))) )?;
        let cases = $crate::lair::expr::CasesE { branches, default };
        let ctrl = $crate::lair::expr::CtrlE::Match($var, cases);
        $crate::lair::expr::BlockE { ops, ctrl }
    }};
}
