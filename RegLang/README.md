# Bundled RegLang library

This directory contains the RegLang formal-language and automata library used
by the artifact. The sources retain their author headers crediting Christian
Doczkal and Jan-Oliver Kaiser and their CeCILL-B notices. The upstream project
is [rocq-community/reglang](https://github.com/rocq-community/reglang).

## Provenance

The original upstream commit of this bundled copy is unknown. A comparison on
2026-11-14 against the
[v1.2.2 source tree](https://github.com/rocq-community/reglang/tree/v1.2.2/theories)
found the following differences. The tag serves as a comparison baseline;
it does not identify the bundled copy as that release.

| Bundled files | Comparison with upstream v1.2.2 |
| --- | --- |
| `languages.v`, `minimization.v`, `misc.v`, `myhill_nerode.v`, `nfa.v`, `shepherdson.v`, `two_way.v`, `vardi.v`, `wmso.v` | All nine files have identical Git blob hashes. |
| `dfa.v` | Omits the `Setoid` import; uses `residual` and `residualP` where upstream uses `residual_lang` and `residual_langP`; uses the local proof name `f'` where upstream uses `g`. |
| `regexp.v` | Ends after `regular_rev`, omitting the appended regular-expression derivative section in v1.2.2. |
| `setoid_leq.v` | Omits `BinPos` from the standard-library imports. |

The three differing files also differ in final blank lines. This comparison
records the current source contents; the history and authorship of the
differences remain unknown.

## License

The bundled RegLang sources are distributed under **CeCILL-B**, as stated in
their existing headers. [LICENSE](LICENSE) reproduces the
[upstream license text](https://github.com/rocq-community/reglang/blob/v1.2.2/LICENSE).
This license covers the bundled library. Choosing a license for the
project-owned artifact code remains an author decision.

## Build and verification

All twelve `.v` files are listed in [../_CoqProject](../_CoqProject) and rebuilt
from source by `make` in the parent directory. The build maps this directory
to the logical namespace `RegLang` and uses these sources in place of a
system-installed RegLang binary.

`make check-sources` includes every bundled source in its scan for proof holes
and new global assumptions. `make check` additionally runs `coqchk` on the
artifact's audit and example modules, checking their imported RegLang
dependencies. See [../README.md](../README.md) for the tested toolchain and
the full build commands.
