# Lurk

## Overview

Lurk is a statically scoped dialect of Lisp, influenced by Scheme and Common Lisp. A reference implementation focused on describing and developing the core language can be found in the [`lurk-lisp`](https://github.com/argumentcomputer/lurk-lisp) repo.

Lurk's distinguishing feature relative to most programming languages is that correct execution of Lurk programs can be directly proved using SNARKs. The resulting proofs are succinct: they are relatively small, can be verified quickly, and they reveal only the information explicitly contained in the statement to be proved.

For more detailed information, refer to the paper: [https://eprint.iacr.org/2023/369](https://eprint.iacr.org/2023/369)

Lurk's distinguishing feature relative to most SNARK authoring languages is that Lurk is Turing complete, so arbitrary computational claims can be made and proved (subject to resource limitations, obviously). Because Lurk is a Lisp, its code is simply Lurk data, and any Lurk data can be directly evaluated as a Lurk program. Lurk constructs compound data using SNARK-friendly Poseidon hashes, so its data is naturally content-addressable.

The [Lurk User Manual](https://docs.argument.xyz/) covers the information necessary to get started.
And the [demo directory](demo/) contains some simple examples for those who want to see how Lurk programs look like.

## Status

Lurk is currently at version 0.5 and is still going through several improvements in order to deliver the best-in-class experience as a fully fledged Turing-complete ZK programming language.

## Performance

Lurk 0.5 offers a big performance jump from [Lurk Beta](https://argument.xyz/blog/lurk-beta/).
Make sure to check out our [performance blog post](https://argument.xyz/blog/perf-2024/) to see how it compares to other contemporary provers.

## Disclaimer

Early adopters should be aware that Lurk 0.5 is a transient accomplishment towards Lurk 1.0, for which a formal audit process is expected.
In the meantime, we invite you to know and experiment Lurk but we don't recommend using it to build critical systems.
