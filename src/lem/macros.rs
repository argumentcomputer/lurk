#[macro_export]
macro_rules! func {
    (fn $name:ident($( $in:ident ),*): $size:literal $lem:tt) => {
        $crate::lem::expr::FuncE {
            name: $crate::lem::Name(stringify!($name)),
            input_params: [$($crate::var!($in)),*].into(),
            output_size: $size,
            body: $crate::block!($lem),
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
    (@seq {$($limbs:expr)*}, let $tgt:ident = num($a:literal) ; $($tail:tt)*) => {
        $crate::block! (
            @seq
            {
                $($limbs)*
                $crate::lem::expr::OpE::Const(
                    $crate::var!($tgt),
                    $crate::lem::field_from_i32($a),
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
                $crate::lem::expr::OpE::Add(
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
                $crate::lem::expr::OpE::Sub(
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
                $crate::lem::expr::OpE::Mul(
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
                $crate::lem::expr::OpE::Inv(
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
                $crate::lem::expr::OpE::Div(
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
                    let func = $crate::lem::Name(stringify!($func));
                    let out = [$($crate::var!($tgt)),*].into();
                    let inp = [$($crate::var!($arg)),*].into();
                    $crate::lem::expr::OpE::Call(out, func, inp)
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
                    let func = $crate::lem::Name(stringify!($func));
                    let out = [$crate::var!($tgt)].into();
                    let inp = [$($crate::var!($arg)),*].into();
                    $crate::lem::expr::OpE::Call(out, func, inp)
                }
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
                            $crate::lem::field_from_i32($num),
                            $crate::block!( $branch )
                        ));
                        $(
                            vec.push((
                                $crate::lem::field_from_i32($other_num),
                                $crate::block!( $branch ),
                            ));
                        )*
                    )*
                }
                let branches = $crate::lem::map::Map::from_vec(vec);
                let default = None $( .or (Some(Box::new($crate::block!( @seq {} , $($def)* )))) )?;
                let cases = $crate::lem::expr::CasesE { branches, default };
                $crate::lem::expr::CtrlE::Match($crate::var!($var), cases)
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
                $crate::lem::expr::CtrlE::If(x, true_block, false_block)
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
                $crate::lem::expr::CtrlE::If(x, false_block, true_block)
            }
        )
    };
    (@seq {$($limbs:expr)*}, return ($($src:ident),*) $(;)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::lem::expr::CtrlE::Return([$($crate::var!($src)),*].into())
        )
    };
    (@seq {$($limbs:expr)*}, return $src:ident $(;)?) => {
        $crate::block! (
            @end
            {
                $($limbs)*
            },
            $crate::lem::expr::CtrlE::Return([$crate::var!($src)].into())
        )
    };
    (@end {$($limbs:expr)*}, $cont:expr) => {
        {
            let ops = [$($limbs),*].into();
            let ctrl = $cont;
            $crate::lem::expr::BlockE{ ops, ctrl }
        }
    }
}

#[macro_export]
macro_rules! var {
    ($variable:ident) => {
        $crate::lem::expr::Var(stringify!($variable))
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
