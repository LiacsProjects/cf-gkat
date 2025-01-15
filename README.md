# Artifact documentation

This is the software artifact accompanying the article _CF-GKAT: Efficient
Validation of Control-Flow Transformations_. This file lists the claims made
in the paper, as well as the steps necessary to reproduce them.


## Claims

The current version of the manuscript makes the following claims:

1. Our blinder is able to handle 836 out of 1425 functions in coreutils 9.5
2. For the `mp_factor_using_pollard_rho` function in `src/factor.c` of
   coreutils 9.5, the following experiments succeed:
   1. Blinding the function using our blinder, compiling the blinded version
      with clang, decompiling it using Ghidra, and then comparing the blinded
      original to a slightly tweaked version of the decompiled code using the
      equivalence checker. In particular, the last step (which concerns our
      contribution) completes in less than a second.
   2. Blinding the function using our blinder, factoring out the `goto`
      statement using calipso, and then comparing the blinded original to
      the `goto`-less code using the equivalence checker. As before, the final
      step, which concerns our contribution, completes in less than a second.
3. We have formalized the following claims in Coq:
   1. Theorem 3.13 (Correctness of lowering). For a CF-GKAT automaton A and an
      indicator value i, we can construct a GKAT automaton A↓ such that the
      translation commutes with the semantics, that is ⟦A↓ᵢ⟧ = ⟦A⟧↓ᵢ^♯.
   2. Theorem 3.19 (Correctness of the Thompson construction). Given an
      expression e, we can construct a CF-GKAT automaton Aₑ such that ⟦e⟧ =
      ⟦Aₑ⟧, i.e., ⟦e⟧ᵢ^ℓ = ⟦Aₑ⟧ᵢ^ℓ for all indicator values i and all labels ℓ,
      including the special label ♯ for the program start.

While preparing this artifact, we realized that the claims above need to be
amended ever so slightly. Specifically:

* When repeating the experiment for Claim 1 in the Docker container, a somewhat
  lower number of functions can be handled by our blinder, than on our host
  machine, namely 797 instead of 836. We suspect the difference is due to a
  different version of Clang, Clangml or OCaml in the Ubuntu version used in
  our container, because our blinder relies on Clangml, the OCaml bindings for
  Clang's parser.
* When repeating the experiments for Claim 2 on older hardware, we found that
  the equivalence checker needs about 30 seconds to run, rather than completing
  in less than a second.

We commit to amending article to reflect the updated version of these claims.


## Installation

This artifact is packaged using a Docker image, and tested on the Linux/amd64
and Linux/x86_64 platforms. We did not have access to Apple silicon to build or
test the image there, and so we recommend using one of these for evaluation.

### Requirements

The following software is necessary to build the Docker image:

1. Docker version 27.2.1 or later
2. The Buildx plugin for Docker, version 0.17 or later

Additionally, a machine with sufficiently large RAM is recommended. During
preparation, it was found that 4GB of RAM is sometimes not enough to build
the image while other software (e.g., a browser) is running, in which case
the OOM killer of the host kernel might step in, and the build will fail.

The fully built image takes up rougly 8.1GB of hard disk space. If the system
building the image runs out of space, the build will fail with errors that can
be hard to debug, depending on the phase of the build.

###  Building the image

To build the image, run the following command in this directory:

```
docker buildx build . -t cf-gkat
```

This command should finish in roughly 20 minutes.


## Evaluation

We now detail how to evaluate the claims made in the paper. The commands listed
below are assumed to be executed inside the Docker image. To obtain a shell,
run the following command after building the image:

```
docker run -it cf-gkat
```

### Claim 1: Blinder coverage

The blinder can be run using the wrapper script `peakyblinders.sh`

```
python3 peakyblinders.py <source dir> <blinder dir> <output dir> <report CSV>
```

So, to run the blinder on coreutils-9.5 (included in the image), run:

```
python3 peakyblinders.py \
    coreutils-9.5 \
    KAT_Decompile \
    coreutils-9.5-blinded \
    coreutils-9.5-blinded.csv
```

This should take roughly 2 minutes, and will output the blinded version of each
function in `coreutils-9.5/src` into a file of the same name in
`coreutils-9.5-blinded/src`. You can compare the blinded and original version
by comparing the contents of these files.

As mentioned in the paper, not every function can be blinded because our
blinder supports only a subset of C. Specifically, statements like `switch` or
`continue` are not supported. When a function cannot be blinded, it will not
appear in the blinded version of the source code file.

The CSV report of the blinding process includes a list of filenames and 
functions per file, in addition to the blinding result (1 for success and 0 for 
failure) and optional information about what variable was detected as an 
indicator variable, if any. The image includes the `csvkit` package, and the 
`csvstat` utility will show information about the run:

```
csvstat -c 3 coreutils-9.5-blinded.csv
```

Here, the number of occurrences of `True` is the number of functions that were
succesfully blinded.

### Claim 2: Experiments

The experiments below assume that the blinding script was run on coreutils. For
more information on how to do this, refer to the steps necessary to evaluate
the previous claim. The commands under this claim should all be run inside
the directory `coreutils-9.5-blinded/src`.

The experiments concern the function `mp_factor_using_pollard_rho` in
`factor.c`. To focus on this file, we isolated the blinded version of this
function into `pollard_rho.c`, found inside `coreutils-9.5-blinded/src`. You
can compare `factor.c` to `pollard_rho.c` to see that all we did was isolate
this function by running:

```
diff -u factor.c pollard_rho.c --color=always | less -R
```

#### Claim 2.1: Compilation-decompilation of `mp_factor_using_pollard_rho`

To compile `pollard_rho.c`, run:

```
clang -c pollard_rho.c -o pollard_rho.o
```

This should complete instantly, and produce a file `pollard_rho.o` in the same
directory. This is the compiled-but-not-linked version of `pollard_rho.c`.

To decompile this file, run the following command, which invokes Ghidra and
writes the decompiled source code back to `pollard_rho-decompiled.c`:

```
/opt/ghidra/support/analyzeHeadless \
    . \
    coreutils \
    -import pollard_rho.o \
    -postscript ../../decompile.py
```

This will take a minute or so.

The Ghidra decompilation includes some artifacts; specifically, Ghidra tends to
assign boolean values to a temporary variable before reading them. This will
throw off the equivalence checker. We need to adjust the output manually to
make the comparison work, so parts like

```
bVar1 = pbool(0x4a);
if ((bVar1 & 1) != 0) {
  ...
}
```

are turned into the equivalent

```
if (pbool(0x4a)) {
  ...
}
```

This is sound because variables like `bVar1` created by Ghidra are always
assigned to right before they are used.

You can make this adjustment to `pollard_rho-decompiled.c` manually, but for
convenience we have included `pollard_rho-clean.c`. To check that
only modifications of the type described above were performed, you can run

```
diff -u pollard_rho-decompiled.c pollard_rho-clean.c --color=always | less -R
```

You can then compare the original (blinded) file to the file obtained by
compiling, decompiling and adjusting by running the following command:

```
../../KAT_Decompile/_build/default/frontend/comparecfgkat.exe \
    pollard_rho.c \
    pollard_rho-clean.c
```

This should complete within a minute. The output should contain a line saying
`Function mp_factor_using_pollard_rho true` to signal that these functions are
equivalent according to the equivalence checker.

#### Claim 2.2: Goto removal in `mp_factor_using_pollard_rho`

This experiment is similar to the previous experiment, except that instead
of compilation followed by decompilation, we run `calipso`, a program that is
meant to remove `goto` statements.

First, you should update your path to include opam's binaries:

```
eval $(opam env)
```

To remove the `goto` statements from `pollard_rho.c`, run the following:

```
calipso pollard_rho.c -o pollard_rho-nogoto.c
```

To compare the original (blinded) file to the version where `goto` statements
are removed, you can run the following command:

```
../../KAT_Decompile/_build/default/frontend/comparecfgkat.exe \
    pollard_rho.c \
    pollard_rho-nogoto.c
```

This should complete within a minute. The output is similar to the previous
experiment. In particular, the line `Function mp_factor_using_pollard_rho true`
should be included in the output.

### Claim 3: Coq formalization

The Coq formalization is fairly minimal, and does not have any dependencies
other than Coq itself (at least version 8.18). If you have Coq installed on
your local machine, you should also be able to open `formalization/main.v` in
your favorite IDE and step through the proofs interactively. For the sake of
completeness, the Docker image also comes bundled with Coq version 8.18.

To verify that all proofs are type-checked, run the following in the main
directory of the artifact:

```
coqc formalization/main.v
```

This command should complete within at most one minute. On Coq version 8.18
(inside the container) and 8.19, no warnings are printed. This command does
give some output about the main claims and their supporting assumptions to
verify that no unwarranted assumptions were admitted. In general, each major
fact is followed by a `Check` vernacular, announcing the claim of the type, and
a `Print Assumptions` vernacular, which prints the facts that need to be
admitted into the core calculus to verify the proof.

In general, the Coq formalization relies on the following extensions of the
calculus of inductive constructions, all of which are in the standard library:
* Propositional extensionality, via `propositional_extensionality`
* Dependent functional extensionality, via `functional_extensionality_dep`
* Streicher's axiom K, equivalent to `Eqdep.Eq_rect_eq.eq_rect_eq`

You will see these assumptions pop up when running the command above. For more
information on the expected output, see the detailed descriptions below.

#### About the encoding

To fully understand the formalized theorems below, we include some remarks on
how the notions from the paper are encoded into Coq.

* The global context includes the type variables `Action`, `Test`, `Label` and
  `IndicatorValue`. These correspond to the sets Σ, T, L and I from the paper.
* Atoms (Definition 2.2) are encoded as predicates on tests, which hold for
  tests included in the atom and are false for the ones that are not. Compound
  tests are encoded via the type `CFGKATTest`, which is a predicate on atoms. 
* The syntax of CF-GKAT is encoded using the inductive `CFGKATExpression`.
  Instances of CFGKATTest fill the role of tests in the syntax.
* The semantics of CF-GKAT expressions is encoded using the fixpoint function
  `cfgkat_expression_semantics`. This calls out to several constructions that
  compose guarded languages with continuations, such as the inductive
  `GuardedLanguageWithContinuationsLabeledFamilySequence`, as described in
  Section 2.2-2.4 of the paper. Note that the semantics for `while` loops is
  defined using two separate constructions, looping and grounding --- the
  former iterates the loop, while the latter takes care of turning
  continuations of the form `brk i` into continuations of the form `acc i`.
* The conversion of (labeled and indexed families of) guarded languages with
  continuations to (labeled and indexed families of) guarded languages as
  described in Section 2.6 of the paper corresponds to the inductive
  `ResolveGuardedLanguageWithContinuationsLabeledFamily`.
* CF-GKAT automata as in Definition 3.5 (resp. GKAT automata; Definition 3.1)
  are encoded using the record type `CFGKATAutomaton` (resp.  `GKATAutomaton`).
  This record consists of all the requisite parts. Note that dynamics are
  encoded as a relation between atoms and indicators on the one hand, and
  outputs on the other. This eases the encoding of most constructions, but also
  means that we have to carry around a proof that the these relations are
  functional. This is encoded in the `CFGKATAutomatonWellFormed` (resp.
  `GKATAutomatonWellFormed`) compound predicates.

#### Claim 3.1: Correctness of lowering

The construction that lowers a CF-GKAT automaton into a GKAT automaton is
encoded in `lower_cfgkat_automaton`, which corresponds to Theorem 3.13 and uses
the inductive predicate `ResolveCFGKATAutomatonDynamics` to convert the
dynamics of a CF-GKAT automaton into one that works for a GKAT automaton.

The lemma `lower_cfgkat_automaton_preserves_wellformed` shows that well-formed
GKAT automata are lowered into well-formed CF-GKAT automata, and the theorem
`lower_cfgkat_automaton_correct` proves that the lowering of the language of
a CF-GKAT automaton is exactly the language of the lowered CF-GKAT automaton.

For `lower_cfgkat_automaton_preserves_wellformed`, the following output is
expected:

```
lower_cfgkat_automaton_preserves_wellformed
     : forall (aut : CFGKATAutomaton) (i : IndicatorValue),
       CFGKATAutomatonWellFormed aut ->
       GKATAutomatonWellFormed (lower_cfgkat_automaton aut i)

Axioms:
Test : Type
Label : Type
IndicatorValue : Type
Action : Type
```

Specifically, this fact does not assume anything other than the types in the
global scope (and would be closed under the global context if we parametrized
them using the `Section` mechanism).

For `lower_cfgkat_automaton_correct`, the following output is expected:

```
lower_cfgkat_automaton_correct
     : forall (aut : CFGKATAutomaton) (i : IndicatorValue),
       gkat_language (lower_cfgkat_automaton aut i) =
       ResolveGuardedLanguageWithContinuationsLabeledFamily
         (cfgkat_languages aut) (cfgkat_language_initial aut) i

Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
Test : Type
Label : Type
IndicatorValue : Type
Action : Type
```

That is, the theorem relies on the three extensions of Coq's theory listed
above, as well as the presence of the four global parameters.

#### Claim 3.2: Correctness of the Thompson construction

The construction that converts a CF-GKAT expression into a CF-GKAT automaton
is encoded in the fixpoint `thompson_construction`. This function calls out
to various constructions that can compose CF-GKAT automata in a way that
matches certain syntactic constructions, such as `cfgkat_automaton_sequence`
for sequential composition of expressions.

The symbol `thompson_construction_correct` corresponds to Theorem 3.19 in the
paper. Its proof calls out to various correctness proofs that show how the
constructions on guarded languages with continuations correspond to relevant
operations on CF-GKAT automata, such as `cfgkat_automaton_sequence_correct`.

The output expected from the vernacular statements following this theorem is:

```
thompson_construction_correct
     : forall e : CFGKATExpression,
       cfgkat_language (thompson_construction e) =
       cfgkat_expression_semantics e

Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
Test : Type
Label : Type
IndicatorValue : Type
Action : Type
```

This theorem thus depends on the same variables in context, as well as the
same extensions of the theory as `lower_cfgkat_automaton_correct`.

In addition to the correctness theorem, our encoding also necessitates that we
check that the Thompson construction produces a well-formed CF-GKAT automaton.
This is done by the lemma `thompson_construction_wellformed`. The structure
of the proof is the same, calling out to proofs that the constructions on
CF-GKAT automata used by the Thompson construction preserve well-formedness.

The output expected from the vernacular statements following this lemma is:

```
thompson_construction_wellformed
     : forall e : CFGKATExpression,
       CFGKATExpressionWellFormed e ->
       CFGKATAutomatonWellFormed (thompson_construction e)

Axioms:
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
Test : Type
Label : Type
IndicatorValue : Type
Action : Type
```

That is, this lemma depends only on Streicher's axiom K and the variables that
are assumed to be in scope already.
