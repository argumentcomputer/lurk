#[macro_export]
macro_rules! func {
    (fn $name:ident($( $in:ident ),*): $size:literal $lair:tt) => {
        $crate::lair::expr::FuncE {
            name: $crate::lair::Name(stringify!($name)),
            invertible: false,
            input_params: [$($crate::var!($in)),*].into(),
            output_size: $size,
            body: $crate::block!($lair),
        }
    };
    (invertible fn $name:ident($( $in:ident ),*): $size:literal $lair:tt) => {
        $crate::lair::expr::FuncE {
            name: $crate::lair::Name(stringify!($name)),
            invertible: true,
            input_params: [$($crate::var!($in)),*].into(),
            output_size: $size,
            body: $crate::block!($lair),
        }
    };
}

#[macro_export]
macro_rules! block {
    // seq entry point, with a separate bracketing to differentiate
    ({ $($body:tt)+ }) => {
        {
            $crate::block! ( @seq {}, $($body)* )
        }
    };
    // handle the recursion: as we see a statement, we push it to the limbs position in the pattern
    (@seq {$($limbs:expr)*}, let $tgt:ident = $a:literal ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Const(
                    $crate::var!($tgt),
                    $crate::lair::field_from_i32($a),
                )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = add($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Add(
                    $crate::var!($tgt),
                    $crate::var!($a),
                    $crate::var!($b),
                )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = sub($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Sub(
                    $crate::var!($tgt),
                    $crate::var!($a),
                    $crate::var!($b),
                )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = mul($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Mul(
                    $crate::var!($tgt),
                    $crate::var!($a),
                    $crate::var!($b),
                )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = not($a:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Not(
                    $crate::var!($tgt),
                    $crate::var!($a),
                )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = eq($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Eq(
                    $crate::var!($tgt),
                    $crate::var!($a),
                    $crate::var!($b),
                )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = inv($a:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Inv(
                    $crate::var!($tgt),
                    $crate::var!($a),
                )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = div($a:ident, $b:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Div(
                    $crate::var!($tgt),
                    $crate::var!($a),
                    $crate::var!($b),
                )
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($($tgt:ident),*) = call($func:ident, $($arg:ident),*) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                {
                    let func = $crate::lair::Name(stringify!($func));
                    let out = [$($crate::var!($tgt)),*].into();
                    let inp = [$($crate::var!($arg)),*].into();
                    $crate::lair::expr::OpE::Call(out, func, inp)
                }
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = call($func:ident, $($arg:ident),*) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                {
                    let func = $crate::lair::Name(stringify!($func));
                    let out = [$crate::var!($tgt)].into();
                    let inp = [$($crate::var!($arg)),*].into();
                    $crate::lair::expr::OpE::Call(out, func, inp)
                }
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($($tgt:ident),*) = preimg($func:ident, $($arg:ident),*) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                {
                    let func = $crate::lair::Name(stringify!($func));
                    let out = [$($crate::var!($tgt)),*].into();
                    let inp = [$($crate::var!($arg)),*].into();
                    $crate::lair::expr::OpE::PreImg(out, func, inp)
                }
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = preimg($func:ident, $($arg:ident),*) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                {
                    let func = $crate::lair::Name(stringify!($func));
                    let out = [$crate::var!($tgt)].into();
                    let inp = [$($crate::var!($arg)),*].into();
                    $crate::lair::expr::OpE::PreImg(out, func, inp)
                }
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let $tgt:ident = store($($arg:ident),*) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                {
                    let out = $crate::var!($tgt);
                    let inp = [$($crate::var!($arg)),*].into();
                    $crate::lair::expr::OpE::Store(out, inp)
                }
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, let ($($tgt:ident),*) = load($arg:ident) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                {
                    let out = [$($crate::var!($tgt)),*].into();
                    let inp = $crate::var!($arg);
                    $crate::lair::expr::OpE::Load(out, inp)
                }
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, debug!($s:literal) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lair::expr::OpE::Debug($s)
            },
            $($tail)*
        )
    };
    (@seq {$($limbs:expr)*}, match $var:ident { $( $num:literal $(| $other_num:literal)* => $branch:tt )* } $(; $($def:tt)*)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            {
                let mut vec = Vec::new();
                {
                    $(
                        vec.push((
                            $crate::lair::field_from_i32($num),
                            $crate::block!( $branch )
                        ));
                        $(
                            vec.push((
                                $crate::lair::field_from_i32($other_num),
                                $crate::block!( $branch ),
                            ));
                        )*
                    )*
                }
                let branches = $crate::lair::map::Map::from_vec(vec);
                let default = None $( .or (Some(Box::new($crate::block!( @seq {} , $($def)* )))) )?;
                let cases = $crate::lair::expr::CasesE { branches, default };
                $crate::lair::expr::CtrlE::Match($crate::var!($var), cases)
            }
        )
    };
    (@seq {$($limbs:expr)*}, if $x:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            {
                let x = $crate::var!($x);
                let true_block = Box::new($crate::block!( @seq {}, $($true_block)+ ));
                let false_block = Box::new($crate::block!( @seq {}, $($false_block)+ ));
                $crate::lair::expr::CtrlE::If(x, true_block, false_block)
            }
        )
    };
    (@seq {$($limbs:expr)*}, if !$x:ident { $($true_block:tt)+ } $($false_block:tt)+ ) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            {
                let x = $crate::var!($x);
                let true_block = Box::new($crate::block!( @seq {}, $($true_block)+ ));
                let false_block = Box::new($crate::block!( @seq {}, $($false_block)+ ));
                $crate::lair::expr::CtrlE::If(x, false_block, true_block)
            }
        )
    };
    (@seq {$($limbs:expr)*}, return ($($src:ident),*) $(;)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::lair::expr::CtrlE::Return([$($crate::var!($src)),*].into())
        )
    };
    (@seq {$($limbs:expr)*}, return $src:ident $(;)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::lair::expr::CtrlE::Return([$crate::var!($src)].into())
        )
    };
    (@end {$($limbs:expr)*}, $cont:expr) => {
        {
            let ops = [$($limbs),*].into();
            let ctrl = $cont;
            $crate::lair::expr::BlockE{ ops, ctrl }
        }
    }
}

#[macro_export]
macro_rules! var {
    ($variable:ident) => {
        $crate::lair::expr::Var(stringify!($variable))
    };
}

#[macro_export]
macro_rules! vars {
    ($($variable:ident),*) => {
        [
            $($crate::var!($variable)),*
        ]
    };
}
