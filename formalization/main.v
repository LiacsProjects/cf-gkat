Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Local Open Scope type_scope.

(* Alphabet parameters *)

Context (Action : Type).
Context (Test : Type).
Context (Label : Type).
Context (IndicatorValue : Type).

Definition Atom := Test -> Prop.

(* Guarded words/languages *)

Inductive GuardedWord :=
| GuardedWordBase: Atom -> GuardedWord
| GuardedWordStep: Atom -> Action -> GuardedWord -> GuardedWord
.

Variant GuardedWordStartsWith (a: Atom): GuardedWord -> Prop :=
| GuardedWordStartsWithBase:
    GuardedWordStartsWith a (GuardedWordBase a)
| GuardedWordStartsWithStep:
    forall (p: Action) (w: GuardedWord),
      GuardedWordStartsWith a (GuardedWordStep a p w)
.

Lemma guarded_word_starts_with_exists
    (w: GuardedWord)
:
    exists a, GuardedWordStartsWith a w
.
Proof.
    destruct w; eexists; constructor.
Qed.

Inductive GuardedConcatenation:
    GuardedWord ->
    GuardedWord ->
    GuardedWord ->
    Prop
:=
| GuardedConcatenationBase:
    forall a,
      GuardedConcatenation
        (GuardedWordBase a)
        (GuardedWordBase a)
        (GuardedWordBase a)
| GuardedConcatenationStep:
    forall a p w x wx,
      GuardedConcatenation w x wx ->
      GuardedConcatenation
        (GuardedWordStep a p w)
        x
        (GuardedWordStep a p wx)
| GuardedConcatenationFuse:
    forall a p w,
      GuardedConcatenation
        (GuardedWordBase a)
        (GuardedWordStep a p w)
        (GuardedWordStep a p w)
.

Lemma guarded_word_starts_with_lift
    (a: Atom)
    (w x wx: GuardedWord)
:
    GuardedWordStartsWith a w ->
    GuardedConcatenation w x wx ->
    GuardedWordStartsWith a wx
.
Proof.
    intros; dependent induction H0; auto.
    all: dependent destruction H; constructor.
Qed.

Lemma guarded_word_starts_with_project
    (a: Atom)
    (w x wx: GuardedWord)
:
    GuardedWordStartsWith a wx ->
    GuardedConcatenation w x wx ->
    GuardedWordStartsWith a w
.
Proof.
    intros.
    dependent destruction H0;
    dependent destruction H; constructor.
Qed.

Lemma guarded_word_concat_last
    (w x: GuardedWord)
    (a: Atom)
:
    GuardedConcatenation w (GuardedWordBase a) x ->
    w = x
.
Proof.
    intros.
    dependent induction H; auto.
    now erewrite IHGuardedConcatenation.
Qed.

Lemma guarded_concatenation_functional:
  forall w x y y',
    GuardedConcatenation w x y ->
    GuardedConcatenation w x y' ->
    y = y'
.
Proof.
  intros.
  dependent induction w.
  - dependent induction x.
    + dependent destruction H.
      dependent destruction H0.
      reflexivity.
    + dependent destruction H.
      dependent destruction H0.
      f_equal.
  - dependent destruction H.
    dependent destruction H0.
    f_equal.
    now apply IHw with (x := x).
Qed.

Lemma guarded_concatenation_trivializes_left
    (w x wx: GuardedWord)
    (a: Atom)
:
    GuardedConcatenation (GuardedWordBase a) x wx ->
    x = wx
.
Proof.
    intros.
    now dependent destruction H.
Qed.

Definition GuardedLanguage := GuardedWord -> Prop.

Ltac guarded_language_extensionality :=
    extensionality w;
    apply propositional_extensionality
.

Definition GuardedLanguageIndexedFamily :=
    IndicatorValue ->
    GuardedLanguage
.

Definition GuardedLanguageLabeledFamily (extra: Type) :=
    Label + extra ->
    GuardedLanguageIndexedFamily
.

(* GKAT automata *)

Variant GKATAutomatonOutputs {state: Type} :=
| GKATAutomatonAccept
| GKATAutomatonReject
| GKATAutomatonNext: Action -> state -> GKATAutomatonOutputs
.

Arguments GKATAutomatonOutputs _ : clear implicits.

Definition GKATAutomatonDynamics (states: Type) :=
    Atom ->
    GKATAutomatonOutputs states ->
    Prop
.

Definition gkat_automaton_dynamics_functional
    {state: Type}
    (dynamics: GKATAutomatonDynamics state)
:=
    forall a zeta1 zeta2,
      dynamics a zeta1 ->
      dynamics a zeta2 ->
      zeta1 = zeta2
.

Record GKATAutomaton := {
    gkat_states:
        Type;
    gkat_transitions:
        gkat_states -> GKATAutomatonDynamics gkat_states;
    gkat_initial:
        GKATAutomatonDynamics gkat_states;
}.

Record GKATAutomatonWellFormed (aut: GKATAutomaton) := {
    gkat_transitions_functional:
        forall s, gkat_automaton_dynamics_functional (gkat_transitions aut s);
    gkat_initial_functional:
        gkat_automaton_dynamics_functional (gkat_initial aut);
}.

Inductive GKATAutomatonAccepts (aut: GKATAutomaton) :
    GKATAutomatonDynamics (gkat_states aut) -> GuardedLanguage
:=
| GKATAutomatonAcceptsBase:
    forall (d: GKATAutomatonDynamics (gkat_states aut)) (a: Atom),
      d a GKATAutomatonAccept ->
      GKATAutomatonAccepts aut d (GuardedWordBase a)
| GKATAutomatonAcceptsStep:
    forall (d: GKATAutomatonDynamics (gkat_states aut))
           (a: Atom)
           (p: Action)
           (s: gkat_states aut)
           (w: GuardedWord),
      d a (GKATAutomatonNext p s) ->
      GKATAutomatonAccepts aut (gkat_transitions aut s) w ->
      GKATAutomatonAccepts aut d (GuardedWordStep a p w)
.

Definition gkat_languages
    (aut: GKATAutomaton)
    (s: gkat_states aut)
:=
    GKATAutomatonAccepts aut (gkat_transitions aut s)
.

Definition gkat_language (aut: GKATAutomaton) :=
    GKATAutomatonAccepts aut (gkat_initial aut)
.

(* Guarded words/languages with continuations *)

Variant CFGKATContinuation :=
| CFGKATContinuationAccept: IndicatorValue -> CFGKATContinuation
| CFGKATContinuationBreak: IndicatorValue -> CFGKATContinuation
| CFGKATContinuationReturn: CFGKATContinuation
| CFGKATContinuationJump: IndicatorValue -> Label -> CFGKATContinuation
.

Definition GuardedWordWithContinuation := GuardedWord * CFGKATContinuation.

Definition GuardedLanguageWithContinuations :=
    GuardedWordWithContinuation -> Prop
.

Definition GuardedLanguageWithContinuationsIndexedFamily :=
    IndicatorValue ->
    GuardedLanguageWithContinuations
.

Ltac guarded_language_with_continuations_indexed_family_extensionality :=
    extensionality i;
    let wc := fresh in extensionality wc;
                       destruct wc as (w, c);
    apply propositional_extensionality
.

Definition GuardedLanguageWithContinuationsLabeledFamily (extra: Type) :=
    Label + extra ->
    GuardedLanguageWithContinuationsIndexedFamily
.

Ltac guarded_language_with_continuations_labeled_family_extensionality :=
    extensionality le;
    guarded_language_with_continuations_indexed_family_extensionality
.

Inductive ResolveGuardedLanguageWithContinuationsLabeledFamily
    {extra: Type}
    (LL: GuardedLanguageWithContinuationsLabeledFamily extra)
    (L: GuardedLanguageWithContinuationsIndexedFamily)
:
    GuardedLanguageIndexedFamily
:=
| ResolveGuardedLanguageWithContinuationsLabeledFamilyBaseAccept:
    forall i w j,
      L i (w, CFGKATContinuationAccept j) ->
      ResolveGuardedLanguageWithContinuationsLabeledFamily LL L i w
| ResolveGuardedLanguageWithContinuationsLabeledFamilyBaseReturn:
    forall i w,
      L i (w, CFGKATContinuationReturn) ->
      ResolveGuardedLanguageWithContinuationsLabeledFamily LL L i w
| ResolveGuardedLanguageWithContinuationsLabeledFamilyJump:
    forall l i j w x wx,
      L i (w, CFGKATContinuationJump j l) ->
      ResolveGuardedLanguageWithContinuationsLabeledFamily LL (LL (inl l)) j x ->
      GuardedConcatenation w x wx ->
      ResolveGuardedLanguageWithContinuationsLabeledFamily LL L i wx
.

(* CF-GKAT automata *)

Variant CFGKATAutomatonOutputs {state: Type} :=
| CFGKATAutomatonPause: CFGKATContinuation -> CFGKATAutomatonOutputs
| CFGKATAutomatonNext:
    Action ->
    state ->
    IndicatorValue ->
    CFGKATAutomatonOutputs
.

Arguments CFGKATAutomatonOutputs : clear implicits.

Definition CFGKATAutomatonDynamics (states: Type) :=
    IndicatorValue ->
    Atom ->
    CFGKATAutomatonOutputs states ->
    Prop
.

Definition cfgkat_automaton_dynamics_functional
    {states: Type}
    (dynamics: CFGKATAutomatonDynamics states)
:=
    forall i a zeta1 zeta2,
      dynamics i a zeta1 ->
      dynamics i a zeta2 ->
      zeta1 = zeta2
.

Record CFGKATAutomaton := {
    cfgkat_states:
        Type;
    cfgkat_transitions:
        cfgkat_states -> CFGKATAutomatonDynamics cfgkat_states;
    cfgkat_labels:
        Label -> CFGKATAutomatonDynamics cfgkat_states;
    cfgkat_initial:
        CFGKATAutomatonDynamics cfgkat_states;
}.

Record CFGKATAutomatonWellFormed (aut: CFGKATAutomaton) := {
    cfgkat_transitions_functional:
        forall s, cfgkat_automaton_dynamics_functional (cfgkat_transitions aut s);
    cfgkat_labels_functional:
        forall l, cfgkat_automaton_dynamics_functional (cfgkat_labels aut l);
    cfgkat_initial_functional:
        cfgkat_automaton_dynamics_functional (cfgkat_initial aut);
}.

Inductive CFGKATAutomatonAccepts (aut: CFGKATAutomaton) :
    CFGKATAutomatonDynamics (cfgkat_states aut) ->
    GuardedLanguageWithContinuationsIndexedFamily
:=
| CFGKATAutomatonAcceptsBase:
    forall (d: CFGKATAutomatonDynamics (cfgkat_states aut))
           (i: IndicatorValue)
           (a: Atom)
           (c: CFGKATContinuation),
      d i a (CFGKATAutomatonPause c) ->
      CFGKATAutomatonAccepts aut d i (GuardedWordBase a, c)
| CFGKATAutomatonAcceptsStep:
    forall (d: CFGKATAutomatonDynamics (cfgkat_states aut))
           (i i': IndicatorValue)
           (a: Atom)
           (p: Action)
           (s: cfgkat_states aut)
           (w: GuardedWord)
           (c: CFGKATContinuation),
      d i a (CFGKATAutomatonNext p s i') ->
      CFGKATAutomatonAccepts aut (cfgkat_transitions aut s) i' (w, c) ->
      CFGKATAutomatonAccepts aut d i (GuardedWordStep a p w, c)
.

Variant CFGKATAutomatonAccepts' (aut: CFGKATAutomaton) :
    CFGKATAutomatonOutputs (cfgkat_states aut) ->
    GuardedLanguageWithContinuations
:=
| CFGKATAutomatonAccepts'Base:
    forall (c: CFGKATContinuation) (a: Atom),
        CFGKATAutomatonAccepts' aut
            (CFGKATAutomatonPause c)
            (GuardedWordBase a, c)
| CFGKATAutomatonAccepts'Step:
    forall (s: cfgkat_states aut)
           (p: Action)
           (i: IndicatorValue)
           (a: Atom)
           (w: GuardedWord)
           (c: CFGKATContinuation),
        CFGKATAutomatonAccepts aut (cfgkat_transitions aut s) i (w, c) ->
        CFGKATAutomatonAccepts' aut
            (CFGKATAutomatonNext p s i)
            (GuardedWordStep a p w, c)
.

Lemma cfgkat_automaton_accepts_shift
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i: IndicatorValue)
    (w: GuardedWord)
    (c: CFGKATContinuation)
:
    CFGKATAutomatonAccepts aut d i (w, c) <->
    exists (a: Atom) (zeta: CFGKATAutomatonOutputs (cfgkat_states aut)),
        GuardedWordStartsWith a w /\
        CFGKATAutomatonAccepts' aut zeta (w, c) /\
        d i a zeta
.
Proof.
    split; intros.
    - dependent destruction H;
      repeat eexists;
      try constructor; eauto.
    - destruct H as [? [? [? [? ?]]]].
      dependent destruction H0;
      dependent destruction H;
      econstructor; eauto.
Qed.

Lemma cfgkat_automaton_accepts_invariant
    (aut: CFGKATAutomaton)
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (i: IndicatorValue)
    (d1 d2: CFGKATAutomatonDynamics (cfgkat_states aut))
:
    CFGKATAutomatonAccepts aut d1 i (w, c) ->
    (forall i a zeta, d1 i a zeta -> d2 i a zeta) ->
    CFGKATAutomatonAccepts aut d2 i (w, c)
.
Proof.
    intros.
    dependent destruction w.
    - dependent destruction H.
      now apply CFGKATAutomatonAcceptsBase, H0.
    - dependent destruction H.
      eapply CFGKATAutomatonAcceptsStep; eauto.
Qed.

Definition cfgkat_dynamics
    (aut: CFGKATAutomaton)
    (ls: Label + cfgkat_states aut)
:=
    match ls with
    | inl l => cfgkat_labels aut l
    | inr s => cfgkat_transitions aut s
    end
.

Definition cfgkat_languages
    (aut: CFGKATAutomaton)
    (ls: Label + cfgkat_states aut)
:=
    CFGKATAutomatonAccepts aut (cfgkat_dynamics aut ls)
.

Definition cfgkat_language_initial
    (aut: CFGKATAutomaton)
:=
    CFGKATAutomatonAccepts aut (cfgkat_initial aut)
.

Definition cfgkat_language
    (aut: CFGKATAutomaton)
    (le: Label + unit)
:
    GuardedLanguageWithContinuationsIndexedFamily
:=
    match le with
    | inl l => CFGKATAutomatonAccepts aut (cfgkat_labels aut l)
    | inr _ => cfgkat_language_initial aut
    end
.

Definition cfgkat_automaton_has_label
    (aut: CFGKATAutomaton)
    (l: Label)
:=
    exists i a zeta, cfgkat_labels aut l i a zeta
.

Definition cfgkat_automata_disjoint
    (aut1 aut2: CFGKATAutomaton)
:=
    forall l,
        ~cfgkat_automaton_has_label aut1 l \/
        ~cfgkat_automaton_has_label aut2 l
.

Lemma cfgkat_automaton_merge_shift
    (aut: CFGKATAutomaton)
    (w: GuardedWord)
    (c : CFGKATContinuation)
    (i j: IndicatorValue)
    (d1 d2: CFGKATAutomatonDynamics (cfgkat_states aut))
    (a: Atom)
:
    CFGKATAutomatonAccepts aut d1 i (w, c) ->
    GuardedWordStartsWith a w ->
    (forall zeta, d1 i a zeta -> d2 j a zeta) ->
    CFGKATAutomatonAccepts aut d2 j (w, c)
.
Proof.
    intros.
    dependent destruction H.
    - constructor.
      dependent destruction H0.
      intuition.
    - econstructor; eauto.
      dependent destruction H1.
      intuition.
Qed.


(* CFGKAT automata resolution *)

Inductive ResolveCFGKATAutomatonDynamics
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i: IndicatorValue)
:
    GKATAutomatonDynamics (IndicatorValue * cfgkat_states aut)
:=
| ResolveCFGKATAutomatonDynamicsAccept:
    forall a i',
      d i a (CFGKATAutomatonPause (CFGKATContinuationAccept i')) ->
      ResolveCFGKATAutomatonDynamics aut d i a GKATAutomatonAccept
| ResolveCFGKATAutomatonDynamicsReturn:
    forall a,
      d i a (CFGKATAutomatonPause CFGKATContinuationReturn) ->
      ResolveCFGKATAutomatonDynamics aut d i a GKATAutomatonAccept
| ResolveCFGKATAutomatonDynamicsNext:
    forall a p s i',
      d i a (CFGKATAutomatonNext p s i') ->
      ResolveCFGKATAutomatonDynamics aut d i a
        (GKATAutomatonNext p (i', s))
| ResolveCFGKATAutomatonDynamicsJump:
    forall a l i' zeta,
      d i a (CFGKATAutomatonPause (CFGKATContinuationJump i' l)) ->
      ResolveCFGKATAutomatonDynamics aut (cfgkat_labels aut l) i' a zeta ->
      ResolveCFGKATAutomatonDynamics aut d i a zeta
.

Lemma resolve_dynamics_preserves_functionality
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i: IndicatorValue)
:
    CFGKATAutomatonWellFormed aut ->
    cfgkat_automaton_dynamics_functional d ->
    gkat_automaton_dynamics_functional
        (ResolveCFGKATAutomatonDynamics aut d i)
.
Proof.
  unfold gkat_automaton_dynamics_functional at 1; intros.
  dependent induction H1.
  - dependent induction H2; auto.
    + now specialize (H0 _ _ _ _ H1 H2).
    + now specialize (H0 _ _ _ _ H1 H2).
  - dependent induction H2; auto.
    + now specialize (H0 _ _ _ _ H1 H2).
    + now specialize (H0 _ _ _ _ H1 H2).
  - dependent induction H2; auto.
    + now specialize (H0 _ _ _ _ H1 H2).
    + now specialize (H0 _ _ _ _ H1 H2).
    + specialize (H0 _ _ _ _ H1 H2).
      now inversion H0.
    + dependent induction H3;
      now specialize (H0 _ _ _ _ H1 H2).
  - dependent induction H3; auto.
    + now specialize (H0 _ _ _ _ H1 H3).
    + now specialize (H0 _ _ _ _ H1 H3).
    + now specialize (H0 _ _ _ _ H1 H3).
    + apply IHResolveCFGKATAutomatonDynamics; auto.
      * now apply cfgkat_labels_functional.
      * specialize (H0 _ _ _ _ H1 H3).
        now inversion H0.
Qed.

Lemma resolve_alias
    (aut: CFGKATAutomaton)
    (s: cfgkat_states aut)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i i': IndicatorValue)
    (a: Atom)
    (p: Action)
    (w: GuardedWord)
:
    d i a (CFGKATAutomatonNext p s i') ->
    ResolveGuardedLanguageWithContinuationsLabeledFamily
        (cfgkat_languages aut) (cfgkat_languages aut (inr s)) i' w ->
    ResolveGuardedLanguageWithContinuationsLabeledFamily
        (cfgkat_languages aut) (CFGKATAutomatonAccepts aut d) i
        (GuardedWordStep a p w)
.
Proof.
  intros.
  dependent destruction H0.
  - eapply ResolveGuardedLanguageWithContinuationsLabeledFamilyBaseAccept.
    eapply CFGKATAutomatonAcceptsStep; eauto.
  - eapply ResolveGuardedLanguageWithContinuationsLabeledFamilyBaseReturn.
    eapply CFGKATAutomatonAcceptsStep; eauto.
  - eapply ResolveGuardedLanguageWithContinuationsLabeledFamilyJump; eauto.
    + eapply CFGKATAutomatonAcceptsStep; eauto.
    + apply GuardedConcatenationStep; eauto.
Qed.

Program Definition lower_cfgkat_automaton
    (aut: CFGKATAutomaton)
    (i: IndicatorValue)
:
    GKATAutomaton
:= {|
  gkat_states := IndicatorValue * cfgkat_states aut;
  gkat_transitions '(i', s) :=
    ResolveCFGKATAutomatonDynamics aut (cfgkat_transitions aut s) i';
  gkat_initial :=
    ResolveCFGKATAutomatonDynamics aut (cfgkat_initial aut) i;
|}.

Lemma lower_cfgkat_automaton_preserves_wellformed
    (aut: CFGKATAutomaton)
    (i: IndicatorValue)
:
    CFGKATAutomatonWellFormed aut ->
    GKATAutomatonWellFormed (lower_cfgkat_automaton aut i)
.
Proof.
    split; intros.
    - destruct s; simpl.
      apply resolve_dynamics_preserves_functionality; auto.
      now apply cfgkat_transitions_functional.
    - apply resolve_dynamics_preserves_functionality; auto.
      now apply cfgkat_initial_functional.
Qed.

Check lower_cfgkat_automaton_preserves_wellformed.
Print Assumptions lower_cfgkat_automaton_preserves_wellformed.

Lemma lower_cfgkat_automaton_concat
    (aut: CFGKATAutomaton)
    (i0 i j: IndicatorValue)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (l: Label)
    (w x wx: GuardedWord)
:
    GuardedConcatenation w x wx ->
    CFGKATAutomatonAccepts aut d i (w, CFGKATContinuationJump j l) ->
    GKATAutomatonAccepts (lower_cfgkat_automaton aut i0)
      (ResolveCFGKATAutomatonDynamics aut (cfgkat_labels aut l) j) x ->
    GKATAutomatonAccepts (lower_cfgkat_automaton aut i0)
      (ResolveCFGKATAutomatonDynamics aut d i) wx
.
Proof.
  intros.
  revert d i H0; dependent induction H; intros.
  - dependent destruction H1.
    apply GKATAutomatonAcceptsBase.
    dependent destruction H0.
    now apply ResolveCFGKATAutomatonDynamicsJump with (i' := j) (l := l).
  - dependent destruction H0.
    eapply GKATAutomatonAcceptsStep.
    + apply ResolveCFGKATAutomatonDynamicsNext, H0.
    + now apply IHGuardedConcatenation.
  - dependent destruction H0.
    dependent destruction H1.
    apply GKATAutomatonAcceptsStep with (s := s); auto.
    now apply ResolveCFGKATAutomatonDynamicsJump with (i' := j) (l := l).
Qed.

Lemma lower_cfgkat_automaton_transparent_accept
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i0 i j: IndicatorValue)
    (w: GuardedWord)
:
    CFGKATAutomatonAccepts aut d i (w, CFGKATContinuationAccept j) ->
    GKATAutomatonAccepts (lower_cfgkat_automaton aut i0)
        (ResolveCFGKATAutomatonDynamics aut d i) w
.
Proof.
   revert i j d; simpl; dependent induction w; intros; inversion_clear H.
   - apply GKATAutomatonAcceptsBase; simpl.
     now apply ResolveCFGKATAutomatonDynamicsAccept with (i' := j).
   - apply GKATAutomatonAcceptsStep with (s := (i', s)); eauto; simpl.
     + apply ResolveCFGKATAutomatonDynamicsNext, H0.
     + now apply IHw with (j := j).
Qed.

Lemma lower_cfgkat_automaton_transparent_return
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i0 i: IndicatorValue)
    (w: GuardedWord)
:
    CFGKATAutomatonAccepts aut d i (w, CFGKATContinuationReturn) ->
    GKATAutomatonAccepts (lower_cfgkat_automaton aut i0)
        (ResolveCFGKATAutomatonDynamics aut d i) w
.
Proof.
   revert i d; simpl; dependent induction w; intros; inversion_clear H.
   - apply GKATAutomatonAcceptsBase; simpl.
     now apply ResolveCFGKATAutomatonDynamicsReturn.
   - apply GKATAutomatonAcceptsStep with (s := (i', s)); eauto; simpl.
     + apply ResolveCFGKATAutomatonDynamicsNext, H0.
     + now apply IHw.
Qed.

Lemma lower_cfgkat_automaton_sound_base
    (aut: CFGKATAutomaton)
    (a: Atom)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i0 i : IndicatorValue)
:
    ResolveCFGKATAutomatonDynamics aut d i a GKATAutomatonAccept ->
    ResolveGuardedLanguageWithContinuationsLabeledFamily
      (cfgkat_languages aut) (CFGKATAutomatonAccepts aut d) i
      (GuardedWordBase a)
.
Proof.
  intros; dependent induction H.
  - eapply ResolveGuardedLanguageWithContinuationsLabeledFamilyBaseAccept.
    unfold cfgkat_languages.
    apply CFGKATAutomatonAcceptsBase, H.
  - eapply ResolveGuardedLanguageWithContinuationsLabeledFamilyBaseReturn.
    unfold cfgkat_languages.
    apply CFGKATAutomatonAcceptsBase, H.
  - eapply ResolveGuardedLanguageWithContinuationsLabeledFamilyJump.
    + unfold cfgkat_languages.
      apply CFGKATAutomatonAcceptsBase, H.
    + now apply IHResolveCFGKATAutomatonDynamics.
    + constructor.
Qed.

Lemma lower_cfgkat_automaton_sound
    (aut: CFGKATAutomaton)
    (w: GuardedWord)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i0 i: IndicatorValue)
:
    GKATAutomatonAccepts (lower_cfgkat_automaton aut i0)
      (ResolveCFGKATAutomatonDynamics aut d i) w ->
    ResolveGuardedLanguageWithContinuationsLabeledFamily
      (cfgkat_languages aut)
      (CFGKATAutomatonAccepts aut d) i w
.
Proof.
  dependent induction w; intros.
  - inversion_clear H; simpl in H0.
    now apply lower_cfgkat_automaton_sound_base.
  - inversion_clear H; simpl in H0.
    dependent induction H0.
    + apply resolve_alias with (s:= s0) (i' := i'); auto.
      now apply IHw with (i0 := i0).
    + eapply ResolveGuardedLanguageWithContinuationsLabeledFamilyJump.
      * unfold cfgkat_languages.
        apply CFGKATAutomatonAcceptsBase, H.
      * now eapply IHResolveCFGKATAutomatonDynamics.
      * constructor.
Qed.

Lemma lower_cfgkat_automaton_complete
    (aut: CFGKATAutomaton)
    (i0 i: IndicatorValue)
    (w: GuardedWord)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
:
    ResolveGuardedLanguageWithContinuationsLabeledFamily
      (cfgkat_languages aut)
      (CFGKATAutomatonAccepts aut d) i w ->
    GKATAutomatonAccepts (lower_cfgkat_automaton aut i0)
      (ResolveCFGKATAutomatonDynamics aut d i) w
.
Proof.
  intros; dependent induction H.
  - eapply lower_cfgkat_automaton_transparent_accept, H.
  - eapply lower_cfgkat_automaton_transparent_return, H.
  - apply lower_cfgkat_automaton_concat
      with (w := w) (x:= x) (j := j) (l := l); auto.
Qed.

Lemma lower_cfgkat_automaton_correct_general
    (aut: CFGKATAutomaton)
    (i i0: IndicatorValue)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
:
    GKATAutomatonAccepts (lower_cfgkat_automaton aut i0)
      (ResolveCFGKATAutomatonDynamics aut d i) =
    ResolveGuardedLanguageWithContinuationsLabeledFamily
      (cfgkat_languages aut)
      (CFGKATAutomatonAccepts aut d) i
.
Proof.
  guarded_language_extensionality.
  split; intros.
  - now apply lower_cfgkat_automaton_sound with (i0 := i0).
  - now apply lower_cfgkat_automaton_complete with (i0 := i0).
Qed.

Theorem lower_cfgkat_automaton_correct
  (aut: CFGKATAutomaton)
  (i: IndicatorValue)
:
  gkat_language (lower_cfgkat_automaton aut i) =
  ResolveGuardedLanguageWithContinuationsLabeledFamily
    (cfgkat_languages aut) (cfgkat_language_initial aut) i
.
Proof.
  apply lower_cfgkat_automaton_correct_general.
Qed.

Check lower_cfgkat_automaton_correct.
Print Assumptions lower_cfgkat_automaton_correct.

(* CFGKAT semantics *)

Definition CFGKATTest := Atom -> Prop.

Definition CFGKATTestTrivial (a: Atom) := True.

Inductive CFGKATExpression :=
| CFGKATAssert:
    CFGKATTest ->
    CFGKATExpression
| CFGKATEquals:
    IndicatorValue ->
    CFGKATExpression
| CFGKATAct:
    Action ->
    CFGKATExpression
| CFGKATAssign:
    IndicatorValue ->
    CFGKATExpression
| CFGKATBreak:
    CFGKATExpression
| CFGKATReturn:
    CFGKATExpression
| CFGKATGoto:
    Label ->
    CFGKATExpression
| CFGKATLabel:
    Label ->
    CFGKATExpression
| CFGKATChoice:
    CFGKATTest ->
    CFGKATExpression ->
    CFGKATExpression ->
    CFGKATExpression
| CFGKATSequence:
    CFGKATExpression ->
    CFGKATExpression ->
    CFGKATExpression
| CFGKATLoop:
    CFGKATTest ->
    CFGKATExpression ->
    CFGKATExpression
.

Variant GuardedLanguageWithContinuationsIndexedFamilyTest
    (t: CFGKATTest)
:
    GuardedLanguageWithContinuationsIndexedFamily
:=
| GuardedLanguageWithContinuationsIndexedFamilyTestAccept:
    forall (i: IndicatorValue) (a: Atom),
      t a ->
      GuardedLanguageWithContinuationsIndexedFamilyTest
        t i (GuardedWordBase a, CFGKATContinuationAccept i)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyTest
    (t: CFGKATTest)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyTestAccept:
    forall (a: Atom) (i: IndicatorValue),
        t a ->
        GuardedLanguageWithContinuationsLabeledFamilyTest
          t (inr tt) i (GuardedWordBase a, CFGKATContinuationAccept i)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyAct
    (p: Action)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyActStep:
    forall (a a': Atom) (i: IndicatorValue),
        GuardedLanguageWithContinuationsLabeledFamilyAct
          p (inr tt) i (GuardedWordStep a p (GuardedWordBase a'),
                        CFGKATContinuationAccept i)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyAssign
    (i: IndicatorValue)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyAssignAccept:
    forall (a: Atom) (j: IndicatorValue),
        GuardedLanguageWithContinuationsLabeledFamilyAssign
          i (inr tt) j (GuardedWordBase a, CFGKATContinuationAccept i)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyEquals
    (i: IndicatorValue)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyEqualsAccept:
    forall (a: Atom),
        GuardedLanguageWithContinuationsLabeledFamilyEquals
          i (inr tt) i (GuardedWordBase a, CFGKATContinuationAccept i)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyBreak:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyBreakBreak:
    forall (a: Atom) (i: IndicatorValue),
        GuardedLanguageWithContinuationsLabeledFamilyBreak
          (inr tt) i (GuardedWordBase a, CFGKATContinuationBreak i)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyReturn:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyReturnReturn:
    forall (a: Atom) (i: IndicatorValue),
        GuardedLanguageWithContinuationsLabeledFamilyReturn
          (inr tt) i (GuardedWordBase a, CFGKATContinuationReturn)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyGoto
    (l: Label)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyGotoGoto:
    forall (a: Atom) (i: IndicatorValue),
        GuardedLanguageWithContinuationsLabeledFamilyGoto
          l (inr tt) i (GuardedWordBase a, CFGKATContinuationJump i l)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyLabel
    (l: Label)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyLabelAccept:
    forall (a: Atom) (i: IndicatorValue),
        GuardedLanguageWithContinuationsLabeledFamilyLabel
          l (inr tt) i (GuardedWordBase a, CFGKATContinuationAccept i)
| GuardedLanguageWithContinuationsLabeledFamilyLabelOffset:
    forall (a: Atom) (i: IndicatorValue),
        GuardedLanguageWithContinuationsLabeledFamilyLabel
          l (inl l) i (GuardedWordBase a, CFGKATContinuationAccept i)
.

Variant GuardedLanguageWithContinuationsIndexedFamilyChoice
    (t: CFGKATTest)
    (L1: GuardedLanguageWithContinuationsIndexedFamily)
    (L2: GuardedLanguageWithContinuationsIndexedFamily)
:
    GuardedLanguageWithContinuationsIndexedFamily
:=
| GuardedLanguageWithContinuationsIndexedFamilyChoiceLeft:
    forall (a: Atom)
           (w: GuardedWord)
           (c: CFGKATContinuation)
           (i: IndicatorValue),
      L1 i (w, c) ->
      t a ->
      GuardedWordStartsWith a w ->
      GuardedLanguageWithContinuationsIndexedFamilyChoice
        t L1 L2 i (w, c)
| GuardedLanguageWithContinuationsIndexedFamilyChoiceRight:
    forall (a: Atom)
           (w: GuardedWord)
           (c: CFGKATContinuation)
           (i: IndicatorValue),
      L2 i (w, c) ->
      ~t a ->
      GuardedWordStartsWith a w ->
      GuardedLanguageWithContinuationsIndexedFamilyChoice
        t L1 L2 i (w, c)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyChoice
    (t: CFGKATTest)
    (L1: GuardedLanguageWithContinuationsLabeledFamily unit)
    (L2: GuardedLanguageWithContinuationsLabeledFamily unit)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyChoiceStart:
    forall (w: GuardedWord)
           (i: IndicatorValue)
           (c: CFGKATContinuation),
      GuardedLanguageWithContinuationsIndexedFamilyChoice t
        (L1 (inr tt))
        (L2 (inr tt))
        i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilyChoice t
        L1 L2 (inr tt) i (w, c)
| GuardedLanguageWithContinuationsLabeledFamilyChoiceOffsetLeft:
    forall (w: GuardedWord)
           (c: CFGKATContinuation)
           (i: IndicatorValue)
           (l: Label),
      L1 (inl l) i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilyChoice
        t L1 L2 (inl l) i (w, c)
| GuardedLanguageWithContinuationsLabeledFamilyChoiceOffsetRight:
    forall (w: GuardedWord)
           (c: CFGKATContinuation)
           (i: IndicatorValue)
           (l: Label),
      L2 (inl l) i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilyChoice
        t L1 L2 (inl l) i (w, c)
.

Variant GuardedLanguageWithContinuationsIndexedFamilySequence
    (L1: GuardedLanguageWithContinuationsIndexedFamily)
    (L2: GuardedLanguageWithContinuationsIndexedFamily)
:
    GuardedLanguageWithContinuationsIndexedFamily
:=
| GuardedLanguageWithContinuationsIndexedFamilySequenceConcat:
    forall (w x wx: GuardedWord)
           (i j: IndicatorValue)
           (c: CFGKATContinuation),
      L1 i (w, CFGKATContinuationAccept j) ->
      L2 j (x, c) ->
      GuardedConcatenation w x wx ->
      GuardedLanguageWithContinuationsIndexedFamilySequence
        L1 L2 i (wx, c)
| GuardedLanguageWithContinuationsIndexedFamilySequenceBreak:
    forall (w: GuardedWord)
           (i j: IndicatorValue),
      L1 i (w, CFGKATContinuationBreak j) ->
      GuardedLanguageWithContinuationsIndexedFamilySequence
        L1 L2 i (w, CFGKATContinuationBreak j)
| GuardedLanguageWithContinuationsIndexedFamilySequenceReturn:
    forall (w: GuardedWord)
           (i: IndicatorValue),
      L1 i (w, CFGKATContinuationReturn) ->
      GuardedLanguageWithContinuationsIndexedFamilySequence
        L1 L2 i (w, CFGKATContinuationReturn)
| GuardedLanguageWithContinuationsIndexedFamilySequenceJump:
    forall (w: GuardedWord)
           (i j: IndicatorValue)
           (l: Label),
      L1 i (w, CFGKATContinuationJump j l) ->
      GuardedLanguageWithContinuationsIndexedFamilySequence
        L1 L2 i (w, CFGKATContinuationJump j l)
.

Variant GuardedLanguageWithContinuationsIndexedFamilyTrivial:
    GuardedLanguageWithContinuationsIndexedFamily
:=
| GuardedLanguageWithContinuationsIndexedFamilyTrivialAccept:
    forall i a, GuardedLanguageWithContinuationsIndexedFamilyTrivial
      i (GuardedWordBase a, CFGKATContinuationAccept i)
.

Lemma guarded_language_with_continuations_indexed_family_sequence_neutral_left
    (L: GuardedLanguageWithContinuationsIndexedFamily)
:
    GuardedLanguageWithContinuationsIndexedFamilySequence
      GuardedLanguageWithContinuationsIndexedFamilyTrivial L = L
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    split; intros.
    - repeat dependent destruction H.
      dependent destruction H1; congruence.
    - dependent destruction w;
      repeat (econstructor; eauto).
Qed.

Variant GuardedLanguageWithContinuationsLabeledFamilySequence
    (L1: GuardedLanguageWithContinuationsLabeledFamily unit)
    (L2: GuardedLanguageWithContinuationsLabeledFamily unit)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilySequenceStart:
    forall (w: GuardedWord)
           (i: IndicatorValue)
           (c: CFGKATContinuation),
      GuardedLanguageWithContinuationsIndexedFamilySequence
        (L1 (inr tt))
        (L2 (inr tt))
        i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilySequence
        L1 L2 (inr tt) i (w, c)
| GuardedLanguageWithContinuationsLabeledFamilySequenceOffsetLeft:
    forall (w: GuardedWord)
           (i: IndicatorValue)
           (c: CFGKATContinuation)
           (l: Label),
      GuardedLanguageWithContinuationsIndexedFamilySequence
        (L1 (inl l))
        (L2 (inr tt))
        i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilySequence
        L1 L2 (inl l) i (w, c)
| GuardedLanguageWithContinuationsLabeledFamilySequenceOffsetRight:
    forall (w: GuardedWord)
           (i: IndicatorValue)
           (c: CFGKATContinuation)
           (l: Label),
      L2 (inl l) i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilySequence
        L1 L2 (inl l) i (w, c)
.

Inductive GuardedLanguageWithContinuationsIndexedFamilyGround
    (L: GuardedLanguageWithContinuationsIndexedFamily)
:
    GuardedLanguageWithContinuationsIndexedFamily
:=
| GuardedLanguageWithContinuationsIndexedFamilyGroundAccept:
    forall (w: GuardedWord) (i j: IndicatorValue),
      L i (w, CFGKATContinuationAccept j) ->
      GuardedLanguageWithContinuationsIndexedFamilyGround
        L i (w, CFGKATContinuationAccept j)
| GuardedLanguageWithContinuationsIndexedFamilyGroundBreak:
    forall (w: GuardedWord) (i j: IndicatorValue),
      L i (w, CFGKATContinuationBreak j) ->
      GuardedLanguageWithContinuationsIndexedFamilyGround
        L i (w, CFGKATContinuationAccept j)
| GuardedLanguageWithContinuationsIndexedFamilyGroundReturn:
    forall (w: GuardedWord) (i: IndicatorValue),
      L i (w, CFGKATContinuationReturn) ->
      GuardedLanguageWithContinuationsIndexedFamilyGround
        L i (w, CFGKATContinuationReturn)
| GuardedLanguageWithContinuationsIndexedFamilyGroundJump:
    forall (w: GuardedWord) (i j: IndicatorValue) (l: Label),
      L i (w, CFGKATContinuationJump j l) ->
      GuardedLanguageWithContinuationsIndexedFamilyGround
        L i (w, CFGKATContinuationJump j l)
.

Variant GuardedLanguageWithContinuationsLabeledFamilyGround
    (L: GuardedLanguageWithContinuationsLabeledFamily unit)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyGroundStart:
    forall (w: GuardedWord) (i: IndicatorValue) (c: CFGKATContinuation),
      GuardedLanguageWithContinuationsIndexedFamilyGround (L (inr tt)) i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilyGround L (inr tt) i (w, c)
| GuardedLanguageWithContinuationsLabeledFamilyGroundOffset:
    forall (w: GuardedWord)
           (i: IndicatorValue)
           (c: CFGKATContinuation)
           (l: Label),
      GuardedLanguageWithContinuationsIndexedFamilyGround (L (inl l)) i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilyGround L (inl l) i (w, c)
.

Inductive GuardedLanguageWithContinuationsIndexedFamilyLoop
    (t: CFGKATTest)
    (L: GuardedLanguageWithContinuationsIndexedFamily)
:
    GuardedLanguageWithContinuationsIndexedFamily
:=
| GuardedLanguageWithContinuationsIndexedFamilyLoopBase:
    forall (a: Atom)
           (i: IndicatorValue),
      ~t a ->
      GuardedLanguageWithContinuationsIndexedFamilyLoop
        t L i (GuardedWordBase a, CFGKATContinuationAccept i)
| GuardedLanguageWithContinuationsIndexedFamilyLoopStep:
    forall (a: Atom)
           (i j: IndicatorValue)
           (w x wx: GuardedWord)
           (c: CFGKATContinuation),
      t a ->
      GuardedWordStartsWith a w ->
      GuardedConcatenation w x wx ->
      L i (w, CFGKATContinuationAccept j) ->
      GuardedLanguageWithContinuationsIndexedFamilyLoop t L j (x, c) ->
      GuardedLanguageWithContinuationsIndexedFamilyLoop t L i (wx, c)
| GuardedLanguageWithContinuationsIndexedFamilyLoopBreak:
    forall (a: Atom)
           (i j: IndicatorValue)
           (w: GuardedWord),
      t a ->
      GuardedWordStartsWith a w ->
      L i (w, CFGKATContinuationBreak j) ->
      GuardedLanguageWithContinuationsIndexedFamilyLoop
        t L i (w, CFGKATContinuationBreak j)
| GuardedLanguageWithContinuationsIndexedFamilyLoopReturn:
    forall (a: Atom)
           (i: IndicatorValue)
           (w: GuardedWord),
      t a ->
      GuardedWordStartsWith a w ->
      L i (w, CFGKATContinuationReturn) ->
      GuardedLanguageWithContinuationsIndexedFamilyLoop
        t L i (w, CFGKATContinuationReturn)
| GuardedLanguageWithContinuationsIndexedFamilyLoopJump:
    forall (a: Atom)
           (i j: IndicatorValue)
           (w: GuardedWord)
           (l: Label),
      t a ->
      GuardedWordStartsWith a w ->
      L i (w, CFGKATContinuationJump j l) ->
      GuardedLanguageWithContinuationsIndexedFamilyLoop
        t L i (w, CFGKATContinuationJump j l)
.

Lemma guarded_language_with_continuations_indexed_family_loop_fixpoint
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
:
    GuardedLanguageWithContinuationsIndexedFamilyLoop
          t (CFGKATAutomatonAccepts aut (cfgkat_initial aut)) =
    GuardedLanguageWithContinuationsIndexedFamilyChoice t
      (GuardedLanguageWithContinuationsIndexedFamilySequence
          (CFGKATAutomatonAccepts aut (cfgkat_initial aut))
          (GuardedLanguageWithContinuationsIndexedFamilyLoop
            t (CFGKATAutomatonAccepts aut (cfgkat_initial aut))))
      (GuardedLanguageWithContinuationsIndexedFamilyTest CFGKATTestTrivial)
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    split; intros.
    - dependent destruction H.
      + eapply GuardedLanguageWithContinuationsIndexedFamilyChoiceRight; eauto.
        * now apply GuardedLanguageWithContinuationsIndexedFamilyTestAccept.
        * apply GuardedWordStartsWithBase.
      + eapply GuardedLanguageWithContinuationsIndexedFamilyChoiceLeft; eauto.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat; eauto.
        * eapply guarded_word_starts_with_lift; eauto.
      + eapply GuardedLanguageWithContinuationsIndexedFamilyChoiceLeft; eauto.
        eapply GuardedLanguageWithContinuationsIndexedFamilySequenceBreak; eauto.
      + eapply GuardedLanguageWithContinuationsIndexedFamilyChoiceLeft; eauto.
        eapply GuardedLanguageWithContinuationsIndexedFamilySequenceReturn; eauto.
      + eapply GuardedLanguageWithContinuationsIndexedFamilyChoiceLeft; eauto.
        eapply GuardedLanguageWithContinuationsIndexedFamilySequenceJump; eauto.
    - dependent destruction H.
      + dependent destruction H.
        * eapply GuardedLanguageWithContinuationsIndexedFamilyLoopStep with (w := w0); eauto.
          eapply guarded_word_starts_with_project; eauto.
        * eapply GuardedLanguageWithContinuationsIndexedFamilyLoopBreak; eauto.
        * eapply GuardedLanguageWithContinuationsIndexedFamilyLoopReturn; eauto.
        * eapply GuardedLanguageWithContinuationsIndexedFamilyLoopJump; eauto.
      + dependent destruction H.
        dependent destruction H1.
        now apply GuardedLanguageWithContinuationsIndexedFamilyLoopBase.
Qed.

Inductive GuardedLanguageWithContinuationsLabeledFamilyLoop
    (t: CFGKATTest)
    (L: GuardedLanguageWithContinuationsLabeledFamily unit)
:
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
| GuardedLanguageWithContinuationsLabeledFamilyLoopStart:
    forall (w: GuardedWord)
           (c: CFGKATContinuation)
           (i: IndicatorValue),
      GuardedLanguageWithContinuationsIndexedFamilyLoop t (L (inr tt)) i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilyLoop
        t L (inr tt) i (w, c)
| GuardedLanguageWithContinuationsLabeledFamilyLoopOffset:
    forall (w: GuardedWord)
           (c: CFGKATContinuation)
           (l: Label)
           (i: IndicatorValue),
      GuardedLanguageWithContinuationsIndexedFamilySequence
        (L (inl l))
        (GuardedLanguageWithContinuationsIndexedFamilyLoop t (L (inr tt)))
        i (w, c) ->
      GuardedLanguageWithContinuationsLabeledFamilyLoop
        t L (inl l) i (w, c)
.

Fixpoint cfgkat_expression_semantics (e: CFGKATExpression):
    GuardedLanguageWithContinuationsLabeledFamily unit
:=
    match e with
    | CFGKATAssert t =>
      GuardedLanguageWithContinuationsLabeledFamilyTest t
    | CFGKATEquals i =>
      GuardedLanguageWithContinuationsLabeledFamilyEquals i
    | CFGKATAct p =>
      GuardedLanguageWithContinuationsLabeledFamilyAct p
    | CFGKATAssign i =>
      GuardedLanguageWithContinuationsLabeledFamilyAssign i
    | CFGKATBreak =>
      GuardedLanguageWithContinuationsLabeledFamilyBreak
    | CFGKATReturn =>
      GuardedLanguageWithContinuationsLabeledFamilyReturn
    | CFGKATGoto l =>
      GuardedLanguageWithContinuationsLabeledFamilyGoto l
    | CFGKATLabel l =>
      GuardedLanguageWithContinuationsLabeledFamilyLabel l
    | CFGKATChoice t e1 e2 =>
      GuardedLanguageWithContinuationsLabeledFamilyChoice t
        (cfgkat_expression_semantics e1)
        (cfgkat_expression_semantics e2)
    | CFGKATSequence e1 e2 =>
      GuardedLanguageWithContinuationsLabeledFamilySequence
        (cfgkat_expression_semantics e1)
        (cfgkat_expression_semantics e2)
    | CFGKATLoop t e =>
      GuardedLanguageWithContinuationsLabeledFamilyGround (
          GuardedLanguageWithContinuationsLabeledFamilyLoop t
            (cfgkat_expression_semantics e)
      )
    end
.

(* CFGKAT expression well-formedness *)

Inductive CFGKATExpressionLabelFor (l: Label):
    CFGKATExpression -> Prop
:=
| CFGKATExpressionLabelForLabel:
    CFGKATExpressionLabelFor l (CFGKATLabel l)
| CFGKATExpressionLabelForChoiceLeft:
    forall (t: CFGKATTest) (e1 e2: CFGKATExpression),
        CFGKATExpressionLabelFor l e1 ->
        CFGKATExpressionLabelFor l (CFGKATChoice t e1 e2)
| CFGKATExpressionLabelForChoiceRight:
    forall (t: CFGKATTest) (e1 e2: CFGKATExpression),
        CFGKATExpressionLabelFor l e2 ->
        CFGKATExpressionLabelFor l (CFGKATChoice t e1 e2)
| CFGKATExpressionLabelForSequenceLeft:
    forall (e1 e2: CFGKATExpression),
        CFGKATExpressionLabelFor l e1 ->
        CFGKATExpressionLabelFor l (CFGKATSequence e1 e2)
| CFGKATExpressionLabelForSequenceRight:
    forall (e1 e2: CFGKATExpression),
        CFGKATExpressionLabelFor l e2 ->
        CFGKATExpressionLabelFor l (CFGKATSequence e1 e2)
| CFGKATExpressionLabelForLoop:
    forall (t: CFGKATTest) (e: CFGKATExpression),
        CFGKATExpressionLabelFor l e ->
        CFGKATExpressionLabelFor l (CFGKATLoop t e)
.

Definition cfgkat_labels_disjoint
    (e1 e2: CFGKATExpression)
:=
    forall l,
        ~CFGKATExpressionLabelFor l e1 \/ ~CFGKATExpressionLabelFor l e2
.

Inductive CFGKATExpressionWellFormed:
    CFGKATExpression -> Prop
:=
| CFGKATExpressionWellFormedAssert:
    forall (t: CFGKATTest),
      CFGKATExpressionWellFormed (CFGKATAssert t)
| CFGKATExpressionWellFormedEquals:
    forall (i: IndicatorValue),
      CFGKATExpressionWellFormed (CFGKATEquals i)
| CFGKATExpressionWellFormedAct:
    forall (p: Action),
      CFGKATExpressionWellFormed (CFGKATAct p)
| CFGKATExpressionWellFormedAssign:
    forall (i: IndicatorValue),
      CFGKATExpressionWellFormed (CFGKATAssign i)
| CFGKATExpressionWellFormedBreak:
    CFGKATExpressionWellFormed CFGKATBreak
| CFGKATExpressionWellFormedReturn:
    CFGKATExpressionWellFormed CFGKATReturn
| CFGKATExpressionWellFormedGoto:
    forall (l: Label),
      CFGKATExpressionWellFormed (CFGKATGoto l)
| CFGKATExpressionWellFormedLabel:
    forall (l: Label),
      CFGKATExpressionWellFormed (CFGKATLabel l)
| CFGKATExpressionWellFormedChoice:
    forall (t: CFGKATTest) (e1 e2: CFGKATExpression),
      CFGKATExpressionWellFormed e1 ->
      CFGKATExpressionWellFormed e2 ->
      cfgkat_labels_disjoint e1 e2 ->
      CFGKATExpressionWellFormed (CFGKATChoice t e1 e2)
| CFGKATExpressionWellFormedSequence:
    forall (e1 e2: CFGKATExpression),
      CFGKATExpressionWellFormed e1 ->
      CFGKATExpressionWellFormed e2 ->
      cfgkat_labels_disjoint e1 e2 ->
      CFGKATExpressionWellFormed (CFGKATSequence e1 e2)
| CFGKATExpressionWellFormedLoop:
    forall (t: CFGKATTest) (e: CFGKATExpression),
      CFGKATExpressionWellFormed e ->
      CFGKATExpressionWellFormed (CFGKATLoop t e)
.

(* Basic CF-GKAT automata *)

Variant CFGKATAutomatonDynamicsTrivial
    {S: Type}
:
    CFGKATAutomatonDynamics S
:=
| CFGKATAutomatonDynamicsTrivialAccept:
    forall (i: IndicatorValue) (a: Atom),
      CFGKATAutomatonDynamicsTrivial i a
        (CFGKATAutomatonPause (CFGKATContinuationAccept i))
.

Lemma cfgkat_automaton_dynamics_trivial_functional
    {S: Type}
:
    cfgkat_automaton_dynamics_functional
      (CFGKATAutomatonDynamicsTrivial (S := S))
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    dependent destruction H;
    dependent destruction H0.
    reflexivity.
Qed.

Lemma cfgkat_automaton_accepts_trivial
    (aut: CFGKATAutomaton)
:
    CFGKATAutomatonAccepts aut CFGKATAutomatonDynamicsTrivial =
    GuardedLanguageWithContinuationsIndexedFamilyTrivial
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    split; intros.
    - repeat dependent destruction H; constructor.
    - repeat dependent destruction H; repeat constructor.
Qed.


Variant CFGKATAutomatonDynamicsAssert
    {S: Type}
    (t: CFGKATTest)
:
    CFGKATAutomatonDynamics S
:=
| CFGKATAutomatonDynamicsAssertAccept:
    forall (a: Atom) (i: IndicatorValue),
        t a ->
        CFGKATAutomatonDynamicsAssert t i a
          (CFGKATAutomatonPause (CFGKATContinuationAccept i))
.

Lemma cfgkat_automaton_dynamics_assert_functional
    {S: Type}
    (t: CFGKATTest)
:
    @cfgkat_automaton_dynamics_functional S (CFGKATAutomatonDynamicsAssert t)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Variant CFGKATAutomatonDynamicsEmpty
    {X: Type}
:
    CFGKATAutomatonDynamics X
:=
.

Lemma cfgkat_automaton_dynamics_empty_functional
    {S: Type}
:
    @cfgkat_automaton_dynamics_functional S (CFGKATAutomatonDynamicsEmpty)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Definition cfgkat_automaton_assert (t: CFGKATTest) : CFGKATAutomaton := {|
    cfgkat_states := Empty_set;
    cfgkat_initial := CFGKATAutomatonDynamicsAssert t;
    cfgkat_transitions _ := CFGKATAutomatonDynamicsEmpty;
    cfgkat_labels _ := CFGKATAutomatonDynamicsEmpty;
|}.

Lemma cfgkat_automaton_assert_wellformed
    (t: CFGKATTest)
:
    CFGKATAutomatonWellFormed (cfgkat_automaton_assert t)
.
Proof.
    split; simpl; intros.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_assert_functional.
Qed.

Lemma cfgkat_automaton_assert_correct (t: CFGKATTest):
    cfgkat_language (cfgkat_automaton_assert t) =
    GuardedLanguageWithContinuationsLabeledFamilyTest t
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intros.
    - destruct le; simpl in H.
      + repeat dependent destruction H.
      + destruct u; unfold cfgkat_language_initial in H.
        dependent destruction H; simpl in H;
        dependent destruction H.
        now constructor.
    - dependent destruction H.
      unfold cfgkat_language; unfold cfgkat_language_initial.
      now repeat constructor.
Qed.

Variant CFGKATAutomatonDynamicsEquals
    {S: Type}
    (i: IndicatorValue)
:
    CFGKATAutomatonDynamics S
:=
| CFGKATAutomatonDynamicsEqualsAccept:
    forall (a: Atom),
        CFGKATAutomatonDynamicsEquals i i a
          (CFGKATAutomatonPause (CFGKATContinuationAccept i))
.

Lemma cfgkat_automaton_dynamics_equals_functional
    {S: Type}
    (i: IndicatorValue)
:
    @cfgkat_automaton_dynamics_functional S (CFGKATAutomatonDynamicsEquals i)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Definition cfgkat_automaton_equals (i: IndicatorValue) : CFGKATAutomaton := {|
    cfgkat_states := Empty_set;
    cfgkat_initial := CFGKATAutomatonDynamicsEquals i;
    cfgkat_transitions _ := CFGKATAutomatonDynamicsEmpty;
    cfgkat_labels _ := CFGKATAutomatonDynamicsEmpty;
|}.

Lemma cfgkat_automaton_equals_wellformed
    (i: IndicatorValue)
:
    CFGKATAutomatonWellFormed (cfgkat_automaton_equals i)
.
Proof.
    split; simpl; intros.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_equals_functional.
Qed.

Lemma cfgkat_automaton_equals_correct (j: IndicatorValue):
    cfgkat_language (cfgkat_automaton_equals j) =
    GuardedLanguageWithContinuationsLabeledFamilyEquals j
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intros.
    - destruct le; simpl in H.
      + repeat dependent destruction H.
      + destruct u; unfold cfgkat_language_initial in H.
        dependent destruction H; simpl in H;
        dependent destruction H.
        now constructor.
    - dependent destruction H.
      unfold cfgkat_language; unfold cfgkat_language_initial.
      now repeat constructor.
Qed.

Variant CFGKATAutomatonDynamicsAct
    (p: Action)
:
    CFGKATAutomatonDynamics unit
:=
| CFGKATAutomatonDynamicsActStep:
    forall (a: Atom) (i: IndicatorValue),
        CFGKATAutomatonDynamicsAct p i a
          (CFGKATAutomatonNext p tt i)
.

Lemma cfgkat_automaton_dynamics_act_functional
    (p: Action)
:
    cfgkat_automaton_dynamics_functional (CFGKATAutomatonDynamicsAct p)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Definition cfgkat_automaton_act (p: Action) : CFGKATAutomaton := {|
    cfgkat_states := unit;
    cfgkat_initial := CFGKATAutomatonDynamicsAct p;
    cfgkat_transitions _ := CFGKATAutomatonDynamicsTrivial;
    cfgkat_labels _ := CFGKATAutomatonDynamicsEmpty;
|}.

Lemma cfgkat_automaton_act_wellformed
    (p: Action)
:
    CFGKATAutomatonWellFormed (cfgkat_automaton_act p)
.
Proof.
    split; simpl; intros.
    - apply cfgkat_automaton_dynamics_trivial_functional.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_act_functional.
Qed.

Lemma cfgkat_automaton_act_correct (p: Action):
    cfgkat_language (cfgkat_automaton_act p) =
    GuardedLanguageWithContinuationsLabeledFamilyAct p
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intros.
    - destruct le; simpl in H.
      + repeat dependent destruction H.
      + destruct u; unfold cfgkat_language_initial in H.
        dependent destruction H; simpl in H;
        dependent destruction H.
        dependent destruction H0; simpl in H;
        dependent destruction H.
        constructor.
    - dependent destruction H.
      unfold cfgkat_language; unfold cfgkat_language_initial.
      repeat econstructor.
Qed.

Variant CFGKATAutomatonDynamicsAssign
    (i: IndicatorValue)
:
    CFGKATAutomatonDynamics Empty_set
:=
| CFGKATAutomatonDynamicsAssignAccept:
    forall (a: Atom) (j: IndicatorValue),
        CFGKATAutomatonDynamicsAssign i j a
          (CFGKATAutomatonPause (CFGKATContinuationAccept i))
.

Lemma cfgkat_automaton_dynamics_assign_functional
    (i: IndicatorValue)
:
    cfgkat_automaton_dynamics_functional (CFGKATAutomatonDynamicsAssign i)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Definition cfgkat_automaton_assign (i: IndicatorValue) : CFGKATAutomaton := {|
    cfgkat_states := Empty_set;
    cfgkat_initial := CFGKATAutomatonDynamicsAssign i;
    cfgkat_transitions _ := CFGKATAutomatonDynamicsEmpty;
    cfgkat_labels _ := CFGKATAutomatonDynamicsEmpty;
|}.

Lemma cfgkat_automaton_assign_wellformed
    (i: IndicatorValue)
:
    CFGKATAutomatonWellFormed (cfgkat_automaton_assign i)
.
Proof.
    split; simpl; intros.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_assign_functional.
Qed.

Lemma cfgkat_automaton_assign_correct (j: IndicatorValue):
    cfgkat_language (cfgkat_automaton_assign j) =
    GuardedLanguageWithContinuationsLabeledFamilyAssign j
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intros.
    - destruct le; simpl in H.
      + repeat dependent destruction H.
      + destruct u; unfold cfgkat_language_initial in H.
        dependent destruction H; simpl in H;
        dependent destruction H.
        now constructor.
    - dependent destruction H.
      unfold cfgkat_language; unfold cfgkat_language_initial.
      now repeat constructor.
Qed.

Variant CFGKATAutomatonDynamicsBreak:
    CFGKATAutomatonDynamics Empty_set
:=
| CFGKATAutomatonDynamicsBreakBreak:
    forall (a: Atom) (i: IndicatorValue),
        CFGKATAutomatonDynamicsBreak i a
          (CFGKATAutomatonPause (CFGKATContinuationBreak i))
.

Lemma cfgkat_automaton_dynamics_break_functional:
    cfgkat_automaton_dynamics_functional CFGKATAutomatonDynamicsBreak
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Definition cfgkat_automaton_break : CFGKATAutomaton := {|
    cfgkat_states := Empty_set;
    cfgkat_initial := CFGKATAutomatonDynamicsBreak;
    cfgkat_transitions _ := CFGKATAutomatonDynamicsEmpty;
    cfgkat_labels _ := CFGKATAutomatonDynamicsEmpty;
|}.

Lemma cfgkat_automaton_break_wellformed:
    CFGKATAutomatonWellFormed cfgkat_automaton_break
.
Proof.
    split; simpl; intros.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_break_functional.
Qed.

Lemma cfgkat_automaton_break_correct:
    cfgkat_language cfgkat_automaton_break =
    GuardedLanguageWithContinuationsLabeledFamilyBreak
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intros.
    - destruct le; simpl in H.
      + repeat dependent destruction H.
      + destruct u; unfold cfgkat_language_initial in H.
        dependent destruction H; simpl in H;
        dependent destruction H.
        now constructor.
    - dependent destruction H.
      unfold cfgkat_language; unfold cfgkat_language_initial.
      now repeat constructor.
Qed.

Variant CFGKATAutomatonDynamicsReturn:
    CFGKATAutomatonDynamics Empty_set
:=
| CFGKATAutomatonDynamicsReturnReturn:
    forall (a: Atom) (i: IndicatorValue),
        CFGKATAutomatonDynamicsReturn i a
          (CFGKATAutomatonPause CFGKATContinuationReturn)
.

Lemma cfgkat_automaton_dynamics_return_functional:
    cfgkat_automaton_dynamics_functional CFGKATAutomatonDynamicsReturn
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Definition cfgkat_automaton_return : CFGKATAutomaton := {|
    cfgkat_states := Empty_set;
    cfgkat_initial := CFGKATAutomatonDynamicsReturn;
    cfgkat_transitions _ := CFGKATAutomatonDynamicsEmpty;
    cfgkat_labels _ := CFGKATAutomatonDynamicsEmpty;
|}.

Lemma cfgkat_automaton_return_wellformed:
    CFGKATAutomatonWellFormed cfgkat_automaton_return
.
Proof.
    split; simpl; intros.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_return_functional.
Qed.

Lemma cfgkat_automaton_return_correct:
    cfgkat_language cfgkat_automaton_return =
    GuardedLanguageWithContinuationsLabeledFamilyReturn
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intros.
    - destruct le; simpl in H.
      + repeat dependent destruction H.
      + destruct u; unfold cfgkat_language_initial in H.
        dependent destruction H; simpl in H;
        dependent destruction H.
        now constructor.
    - dependent destruction H.
      unfold cfgkat_language; unfold cfgkat_language_initial.
      now repeat constructor.
Qed.

Variant CFGKATAutomatonDynamicsGoto
    (l: Label)
:
    CFGKATAutomatonDynamics Empty_set
:=
| CFGKATAutomatonDynamicsGotoGoto:
    forall (a: Atom) (i: IndicatorValue),
        CFGKATAutomatonDynamicsGoto l i a
          (CFGKATAutomatonPause (CFGKATContinuationJump i l))
.

Lemma cfgkat_automaton_dynamics_goto_functional
    (l: Label)
:
    cfgkat_automaton_dynamics_functional (CFGKATAutomatonDynamicsGoto l)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Definition cfgkat_automaton_goto (l: Label) : CFGKATAutomaton := {|
    cfgkat_states := Empty_set;
    cfgkat_initial := CFGKATAutomatonDynamicsGoto l;
    cfgkat_transitions _ := CFGKATAutomatonDynamicsEmpty;
    cfgkat_labels _ := CFGKATAutomatonDynamicsEmpty;
|}.

Lemma cfgkat_automaton_goto_wellformed
    (l: Label)
:
    CFGKATAutomatonWellFormed (cfgkat_automaton_goto l)
.
Proof.
    split; simpl; intros.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_goto_functional.
Qed.

Lemma cfgkat_automaton_goto_correct (l: Label):
    cfgkat_language (cfgkat_automaton_goto l) =
    GuardedLanguageWithContinuationsLabeledFamilyGoto l
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intros.
    - destruct le; simpl in H.
      + repeat dependent destruction H.
      + destruct u; unfold cfgkat_language_initial in H.
        dependent destruction H; simpl in H;
        dependent destruction H.
        now constructor.
    - dependent destruction H.
      unfold cfgkat_language; unfold cfgkat_language_initial.
      now repeat constructor.
Qed.

Variant CFGKATAutomatonDynamicsLabel
    (l: Label)
:
    Label -> CFGKATAutomatonDynamics Empty_set
:=
| CFGKATAutomatonDynamicsLabelAccept:
    forall (a: Atom) (i: IndicatorValue),
        CFGKATAutomatonDynamicsLabel l l i a
          (CFGKATAutomatonPause (CFGKATContinuationAccept i))
.

Lemma cfgkat_automaton_dynamics_label_functional
    (l l': Label)
:
    cfgkat_automaton_dynamics_functional (CFGKATAutomatonDynamicsLabel l l')
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    now dependent destruction H; dependent destruction H0.
Qed.

Definition cfgkat_automaton_label (l: Label) : CFGKATAutomaton := {|
    cfgkat_states := Empty_set;
    cfgkat_initial := CFGKATAutomatonDynamicsTrivial;
    cfgkat_transitions _ := CFGKATAutomatonDynamicsEmpty;
    cfgkat_labels := CFGKATAutomatonDynamicsLabel l;
|}.

Lemma cfgkat_automaton_label_wellformed
    (l: Label)
:
    CFGKATAutomatonWellFormed (cfgkat_automaton_label l)
.
Proof.
    split; simpl; intros.
    - apply cfgkat_automaton_dynamics_empty_functional.
    - apply cfgkat_automaton_dynamics_label_functional.
    - apply cfgkat_automaton_dynamics_trivial_functional.
Qed.

Lemma cfgkat_automaton_label_correct (l: Label):
    cfgkat_language (cfgkat_automaton_label l) =
    GuardedLanguageWithContinuationsLabeledFamilyLabel l
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intros.
    - destruct le; simpl in H.
      + repeat dependent destruction H.
        repeat constructor.
      + destruct u; unfold cfgkat_language_initial in H.
        dependent destruction H; simpl in H;
        dependent destruction H.
        now constructor.
    - dependent destruction H;
      unfold cfgkat_language; unfold cfgkat_language_initial;
      now repeat constructor.
Qed.

(* Choice composition of automata *)

Inductive CFGKATAutomatonDynamicsMorph
    {X Y: Type}
    (f: X -> Y)
    (d: CFGKATAutomatonDynamics X)
:
    CFGKATAutomatonDynamics Y
:=
| CFGKATAutomatonDynamicsMorphPause:
    forall a i c,
    d i a (CFGKATAutomatonPause c) ->
    CFGKATAutomatonDynamicsMorph f d i a (CFGKATAutomatonPause c)
| CFGKATAutomatonDynamicsMorphNext:
    forall a i j p x,
    d i a (CFGKATAutomatonNext p x j) ->
    CFGKATAutomatonDynamicsMorph f d i a (CFGKATAutomatonNext p (f x) j)
.

Lemma cfgkat_dynamics_morph_preserves_functional
    {X Y: Type}
    (f: X -> Y)
    (d: CFGKATAutomatonDynamics X)
:
    cfgkat_automaton_dynamics_functional d ->
    cfgkat_automaton_dynamics_functional (CFGKATAutomatonDynamicsMorph f d)
.
Proof.
    intros; unfold cfgkat_automaton_dynamics_functional; intros.
    dependent destruction H0.
    - dependent destruction H1.
      + specialize (H _ _ _ _ H0 H1).
        now inversion H.
      + specialize (H _ _ _ _ H0 H1).
        now inversion H.
    - dependent destruction H1.
      + specialize (H _ _ _ _ H0 H1).
        now inversion H.
      + specialize (H _ _ _ _ H0 H1).
        now inversion H.
Qed.

Variant CFGKATAutomatonDynamicsChoice
    {S1 S2: Type}
    (t: CFGKATTest)
    (d1: CFGKATAutomatonDynamics S1)
    (d2: CFGKATAutomatonDynamics S2)
:
    CFGKATAutomatonDynamics (S1 + S2)
:=
| CFGKATAutomatonDynamicsChoiceLeft:
    forall (i: IndicatorValue)
           (a: Atom)
           (zeta: CFGKATAutomatonOutputs (S1 + S2)),
      t a ->
      CFGKATAutomatonDynamicsMorph inl d1 i a zeta ->
      CFGKATAutomatonDynamicsChoice t d1 d2 i a zeta
| CFGKATAutomatonDynamicsChoiceRight:
    forall (i: IndicatorValue)
           (a: Atom)
           (zeta: CFGKATAutomatonOutputs (S1 + S2)),
      ~t a ->
      CFGKATAutomatonDynamicsMorph inr d2 i a zeta ->
      CFGKATAutomatonDynamicsChoice t d1 d2 i a zeta
.

Lemma cfgkat_dynamics_choice_preserves_functional
    {X Y: Type}
    (t: CFGKATTest)
    (d1: CFGKATAutomatonDynamics X)
    (d2: CFGKATAutomatonDynamics Y)
:
    cfgkat_automaton_dynamics_functional d1 ->
    cfgkat_automaton_dynamics_functional d2 ->
    cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsChoice t d1 d2)
.
Proof.
    intros; unfold cfgkat_automaton_dynamics_functional; intros.
    dependent destruction H1.
    - dependent destruction H3; intuition.
      eapply cfgkat_dynamics_morph_preserves_functional.
      + apply H.
      + apply H2.
      + apply H4.
    - dependent destruction H3; intuition.
      eapply cfgkat_dynamics_morph_preserves_functional.
      + apply H0.
      + apply H2.
      + apply H4.
Qed.

Definition CFGKATAutomatonDynamicsChoiceLift
    {S1 S2 T1 T2: Type}
    (d1: T1 -> CFGKATAutomatonDynamics S1)
    (d2: T2 -> CFGKATAutomatonDynamics S2)
    (t: T1 + T2)
:
    CFGKATAutomatonDynamics (S1 + S2)
:=
    match t with
    | inl t => CFGKATAutomatonDynamicsMorph inl (d1 t)
    | inr t => CFGKATAutomatonDynamicsMorph inr (d2 t)
    end
.

Lemma cfgkat_dynamics_choice_lift_preserves_functional
    {S1 S2 T1 T2: Type}
    (d1: T1 -> CFGKATAutomatonDynamics S1)
    (d2: T2 -> CFGKATAutomatonDynamics S2)
:
    (forall s, cfgkat_automaton_dynamics_functional (d1 s)) ->
    (forall s, cfgkat_automaton_dynamics_functional (d2 s)) ->
    forall s, cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsChoiceLift d1 d2 s)
.
Proof.
  intros; unfold cfgkat_automaton_dynamics_functional.
  destruct s; simpl; intros; [clear H0 | clear H];
  eapply cfgkat_dynamics_morph_preserves_functional; eauto.
Qed.

Variant CFGKATAutomatonDynamicsChoiceLabels
    {S1 S2: Type}
    (d1: Label -> CFGKATAutomatonDynamics S1)
    (d2: Label -> CFGKATAutomatonDynamics S2)
:
    Label -> CFGKATAutomatonDynamics (S1 + S2)
:=
| CFGKATAutomatonDynamicsChoiceLabelsLeft:
    forall l a i zeta,
      CFGKATAutomatonDynamicsMorph inl (d1 l) a i zeta ->
      CFGKATAutomatonDynamicsChoiceLabels d1 d2 l a i zeta
| CFGKATAutomatonDynamicsChoiceLabelsRight:
    forall l a i zeta,
      CFGKATAutomatonDynamicsMorph inr (d2 l) a i zeta ->
      CFGKATAutomatonDynamicsChoiceLabels d1 d2 l a i zeta
.

Lemma cfgkat_automata_choice_labels_functional
    (aut1 aut2: CFGKATAutomaton)
    (l: Label)
:
    CFGKATAutomatonWellFormed aut1 ->
    CFGKATAutomatonWellFormed aut2 ->
    cfgkat_automata_disjoint aut1 aut2 ->
    cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsChoiceLabels
            (cfgkat_labels aut1)
            (cfgkat_labels aut2) l)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional; intros.
    dependent destruction H2.
    - dependent destruction H3.
      + eapply cfgkat_dynamics_morph_preserves_functional; eauto.
        eapply cfgkat_labels_functional; eauto.
      + dependent destruction H2; dependent destruction H3;
        specialize (H1 l); firstorder.
    - dependent destruction H3.
      + dependent destruction H2; dependent destruction H3;
        specialize (H1 l); firstorder.
      + eapply cfgkat_dynamics_morph_preserves_functional; eauto.
        eapply cfgkat_labels_functional; eauto.
Qed.

Definition cfgkat_automaton_choice
    (t: CFGKATTest)
    (aut1 aut2: CFGKATAutomaton)
:
    CFGKATAutomaton
:= {|
    cfgkat_states := cfgkat_states aut1 + cfgkat_states aut2;
    cfgkat_transitions :=
        CFGKATAutomatonDynamicsChoiceLift
            (cfgkat_transitions aut1)
            (cfgkat_transitions aut2);
    cfgkat_labels :=
        CFGKATAutomatonDynamicsChoiceLabels
            (cfgkat_labels aut1)
            (cfgkat_labels aut2);
    cfgkat_initial :=
        CFGKATAutomatonDynamicsChoice t
            (cfgkat_initial aut1)
            (cfgkat_initial aut2);
|}.

Lemma cfgkat_automaton_choice_preserves_wellformed
    (t: CFGKATTest)
    (aut1 aut2: CFGKATAutomaton)
:
    CFGKATAutomatonWellFormed aut1 ->
    CFGKATAutomatonWellFormed aut2 ->
    cfgkat_automata_disjoint aut1 aut2 ->
    CFGKATAutomatonWellFormed (cfgkat_automaton_choice t aut1 aut2)
.
Proof.
    split; intros; simpl.
    - apply cfgkat_dynamics_choice_lift_preserves_functional; firstorder.
    - now apply cfgkat_automata_choice_labels_functional.
    - apply cfgkat_dynamics_choice_preserves_functional; firstorder.
Qed.

Lemma cfgkat_automaton_choice_inject_left
    (t: CFGKATTest)
    (aut1 aut2: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut1))
:
    CFGKATAutomatonAccepts
        (cfgkat_automaton_choice t aut1 aut2)
        (CFGKATAutomatonDynamicsMorph inl d) =
    CFGKATAutomatonAccepts aut1 d
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    revert d i; dependent induction w; simpl.
    - split; intros.
      + repeat dependent destruction H.
        now apply CFGKATAutomatonAcceptsBase.
      + dependent destruction H.
        now repeat constructor.
    - split; intros.
      + repeat dependent destruction H.
        eapply CFGKATAutomatonAcceptsStep; eauto; firstorder.
      + dependent destruction H.
        eapply CFGKATAutomatonAcceptsStep.
        * apply CFGKATAutomatonDynamicsMorphNext; eauto.
        * now apply IHw.
Qed.

Lemma cfgkat_automaton_choice_inject_right
    (t: CFGKATTest)
    (aut1 aut2: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut2))
:
    CFGKATAutomatonAccepts
        (cfgkat_automaton_choice t aut1 aut2)
        (CFGKATAutomatonDynamicsMorph inr d) =
    CFGKATAutomatonAccepts aut2 d
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    revert d i; dependent induction w; simpl.
    - split; intros.
      + repeat dependent destruction H.
        now apply CFGKATAutomatonAcceptsBase.
      + dependent destruction H.
        now repeat constructor.
    - split; intros.
      + repeat dependent destruction H.
        eapply CFGKATAutomatonAcceptsStep; eauto; firstorder.
      + dependent destruction H.
        eapply CFGKATAutomatonAcceptsStep.
        * apply CFGKATAutomatonDynamicsMorphNext; eauto.
        * now apply IHw.
Qed.

Lemma cfgkat_automaton_choice_correct_dynamics
    (t: CFGKATTest)
    (aut1 aut2: CFGKATAutomaton)
    (d1: CFGKATAutomatonDynamics (cfgkat_states aut1))
    (d2: CFGKATAutomatonDynamics (cfgkat_states aut2))
:
    CFGKATAutomatonAccepts
        (cfgkat_automaton_choice t aut1 aut2)
        (CFGKATAutomatonDynamicsChoice t d1 d2) =
    GuardedLanguageWithContinuationsIndexedFamilyChoice t
        (CFGKATAutomatonAccepts aut1 d1)
        (CFGKATAutomatonAccepts aut2 d2)
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    split; intros.
    - dependent destruction H.
      + dependent destruction H;
        dependent destruction H0;
        repeat econstructor; now eauto.
      + dependent destruction H;
        dependent destruction H0;
        simpl in H1.
        * eapply GuardedLanguageWithContinuationsIndexedFamilyChoiceLeft;
          eauto; econstructor; eauto.
          erewrite <- cfgkat_automaton_choice_inject_left; eauto.
        * eapply GuardedLanguageWithContinuationsIndexedFamilyChoiceRight;
          eauto; econstructor; eauto.
          erewrite <- cfgkat_automaton_choice_inject_right; eauto.
    - dependent destruction H.
      + dependent destruction H1;
        dependent destruction H.
        * repeat econstructor; now eauto.
        * econstructor.
          -- apply CFGKATAutomatonDynamicsChoiceLeft; eauto.
             constructor; eauto.
          -- simpl; now erewrite cfgkat_automaton_choice_inject_left.
      + dependent destruction H1;
        dependent destruction H.
        * repeat econstructor; now eauto.
        * econstructor.
          -- apply CFGKATAutomatonDynamicsChoiceRight; eauto.
             constructor; eauto.
          -- simpl; now erewrite cfgkat_automaton_choice_inject_right.
Qed.

Lemma cfgkat_automaton_choice_correct_initial
    (t: CFGKATTest)
    (aut1 aut2: CFGKATAutomaton)
:
    cfgkat_language_initial (cfgkat_automaton_choice t aut1 aut2) =
    GuardedLanguageWithContinuationsIndexedFamilyChoice t
        (cfgkat_language_initial aut1) (cfgkat_language_initial aut2)
.
Proof.
    apply cfgkat_automaton_choice_correct_dynamics.
Qed.

Lemma cfgkat_automaton_dynamics_morph_extract
    {S1 S2: Type}
    (d: CFGKATAutomatonDynamics S1)
    (f: S1 -> S2)
    (i: IndicatorValue)
    (a: Atom)
    (zeta: CFGKATAutomatonOutputs S2)
:
    CFGKATAutomatonDynamicsMorph f d i a zeta ->
    exists zeta', d i a zeta'
.
Proof.
    intros; dependent destruction H;
    eexists; eauto.
Qed.

Lemma cfgkat_automaton_choice_correct
    (t: CFGKATTest)
    (aut1 aut2: CFGKATAutomaton)
:
    cfgkat_language (cfgkat_automaton_choice t aut1 aut2) =
    GuardedLanguageWithContinuationsLabeledFamilyChoice t
        (cfgkat_language aut1) (cfgkat_language aut2)
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    destruct le; simpl.
    - split; intros.
      + apply cfgkat_automaton_accepts_shift in H.
        destruct H as [a [zeta [? [? ?]]]].
        dependent destruction H1.
        * apply GuardedLanguageWithContinuationsLabeledFamilyChoiceOffsetLeft.
          unfold cfgkat_language; erewrite <- cfgkat_automaton_choice_inject_left.
          apply cfgkat_automaton_accepts_shift; repeat eexists; eauto.
        * apply GuardedLanguageWithContinuationsLabeledFamilyChoiceOffsetRight.
          unfold cfgkat_language; erewrite <- cfgkat_automaton_choice_inject_right.
          apply cfgkat_automaton_accepts_shift; repeat eexists; eauto.
      + dependent destruction H.
        * eapply cfgkat_automaton_accepts_invariant; intros.
          -- unfold cfgkat_language in H.
             erewrite <- cfgkat_automaton_choice_inject_left in H; eauto.
          -- now constructor.
        * eapply cfgkat_automaton_accepts_invariant; intros.
          -- unfold cfgkat_language in H.
             erewrite <- cfgkat_automaton_choice_inject_right in H; eauto.
          -- now constructor.
    - destruct u; split; simpl; intros.
      + constructor; unfold cfgkat_language; unfold cfgkat_language_initial.
        now erewrite <- cfgkat_automaton_choice_correct_dynamics.
      + dependent destruction H.
        unfold cfgkat_language_initial; simpl.
        now erewrite cfgkat_automaton_choice_correct_dynamics.
Qed.

(* Sequential composition of automata *)

Variant CFGKATAutomatonDynamicsSequence
    {S1 S2: Type}
    (d1: CFGKATAutomatonDynamics S1)
    (d2: CFGKATAutomatonDynamics S2)
:
    CFGKATAutomatonDynamics (S1 + S2)
:=
| CFGKATAutomatonDynamicsSequenceEnterBreak:
    forall (i j: IndicatorValue) (a: Atom),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationBreak j)) ->
      CFGKATAutomatonDynamicsSequence d1 d2 i a
        (CFGKATAutomatonPause (CFGKATContinuationBreak j))
| CFGKATAutomatonDynamicsSequenceEnterReturn:
    forall (i: IndicatorValue) (a: Atom),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationReturn)) ->
      CFGKATAutomatonDynamicsSequence d1 d2 i a
        (CFGKATAutomatonPause (CFGKATContinuationReturn))
| CFGKATAutomatonDynamicsSequenceEnterJump:
    forall (i j: IndicatorValue) (l: Label) (a: Atom),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationJump j l)) ->
      CFGKATAutomatonDynamicsSequence d1 d2 i a
        (CFGKATAutomatonPause (CFGKATContinuationJump j l))
| CFGKATAutomatonDynamicsSequenceEnterNext:
    forall (i j: IndicatorValue) (a: Atom) (p: Action) (s: S1),
      d1 i a (CFGKATAutomatonNext p s j) ->
      CFGKATAutomatonDynamicsSequence d1 d2 i a
        (CFGKATAutomatonNext p (inl s) j)
| CFGKATAutomatonDynamicsSequenceSkip:
    forall (i j: IndicatorValue) (a: Atom)
           (zeta: CFGKATAutomatonOutputs (S1 + S2)),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationAccept j)) ->
      CFGKATAutomatonDynamicsMorph inr d2 j a zeta ->
      CFGKATAutomatonDynamicsSequence d1 d2 i a zeta
.

Lemma cfgkat_dynamics_sequence_preserves_functional
    {X Y: Type}
    (d1: CFGKATAutomatonDynamics X)
    (d2: CFGKATAutomatonDynamics Y)
:
    cfgkat_automaton_dynamics_functional d1 ->
    cfgkat_automaton_dynamics_functional d2 ->
    cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsSequence d1 d2)
.
Proof.
    intros; unfold cfgkat_automaton_dynamics_functional; intros.
    dependent destruction H1;
    try (dependent destruction H2;
         specialize (H _ _ _ _ H1 H2);
         now inversion H).
    dependent destruction H3;
    try (dependent destruction H2;
         specialize (H _ _ _ _ H1 H3);
         now inversion H).
    specialize (H _ _ _ _ H1 H3).
    inversion H; subst.
    eapply cfgkat_dynamics_morph_preserves_functional
      with (d := d2); eauto.
Qed.

Definition CFGKATAutomatonDynamicsSequenceState
    {S1 S2: Type}
    (d1: S1 -> CFGKATAutomatonDynamics S1)
    (i2: CFGKATAutomatonDynamics S2)
    (d2: S2 -> CFGKATAutomatonDynamics S2)
    (s: S1 + S2)
:
    CFGKATAutomatonDynamics (S1 + S2)
:=
    match s with
    | inl s => CFGKATAutomatonDynamicsSequence (d1 s) i2
    | inr s => CFGKATAutomatonDynamicsMorph inr (d2 s)
    end
.

Lemma cfgkat_dynamics_sequence_state_preserves_functional
    {X Y: Type}
    (d1: X -> CFGKATAutomatonDynamics X)
    (i2: CFGKATAutomatonDynamics Y)
    (d2: Y -> CFGKATAutomatonDynamics Y)
:
    (forall s, cfgkat_automaton_dynamics_functional (d1 s)) ->
    cfgkat_automaton_dynamics_functional i2 ->
    (forall s, cfgkat_automaton_dynamics_functional (d2 s)) ->
    forall s, cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsSequenceState d1 i2 d2 s)
.
Proof.
  unfold cfgkat_automaton_dynamics_functional at 4; intros.
  destruct s; simpl in H2, H3.
  - eapply cfgkat_dynamics_sequence_preserves_functional; eauto.
  - eapply cfgkat_dynamics_morph_preserves_functional with (d := d2 y); eauto.
Qed.

Variant CFGKATAutomatonDynamicsSequenceLabels
    {S1 S2: Type}
    (d1: Label -> CFGKATAutomatonDynamics S1)
    (i2: CFGKATAutomatonDynamics S2)
    (d2: Label -> CFGKATAutomatonDynamics S2)
:
    Label -> CFGKATAutomatonDynamics (S1 + S2)
:=
| CFGKATAutomatonDynamicsSequenceLabelsLeft:
    forall l a i zeta,
      CFGKATAutomatonDynamicsSequence (d1 l) i2 i a zeta ->
      CFGKATAutomatonDynamicsSequenceLabels d1 i2 d2 l i a zeta
| CFGKATAutomatonDynamicsSequenceLabelsRight:
    forall l a i zeta,
      CFGKATAutomatonDynamicsMorph inr (d2 l) i a zeta ->
      CFGKATAutomatonDynamicsSequenceLabels d1 i2 d2 l i a zeta
.

Lemma cfgkat_automata_sequence_labels_functional
    (aut1 aut2: CFGKATAutomaton)
    (l: Label)
:
    CFGKATAutomatonWellFormed aut1 ->
    CFGKATAutomatonWellFormed aut2 ->
    cfgkat_automata_disjoint aut1 aut2 ->
    cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsSequenceLabels
            (cfgkat_labels aut1)
            (cfgkat_initial aut2)
            (cfgkat_labels aut2) l)
.
Proof.
  unfold cfgkat_automaton_dynamics_functional; intros.
  dependent destruction H2.
  - dependent destruction H3.
    + eapply cfgkat_dynamics_sequence_preserves_functional; eauto.
      * apply H.
      * apply H0.
    + unfold cfgkat_automata_disjoint in H1.
      specialize (H1 l).
      dependent destruction H2;
      dependent destruction H3;
      try dependent destruction H4;
      firstorder.
  - dependent destruction H3.
    + unfold cfgkat_automata_disjoint in H1.
      specialize (H1 l).
      dependent destruction H2;
      dependent destruction H3;
      try dependent destruction H4;
      firstorder.
    + eapply cfgkat_dynamics_morph_preserves_functional; eauto.
      apply H0.
Qed.

Definition cfgkat_automaton_sequence
    (aut1 aut2: CFGKATAutomaton)
:
    CFGKATAutomaton
:= {|
    cfgkat_states := cfgkat_states aut1 + cfgkat_states aut2;
    cfgkat_transitions :=
        CFGKATAutomatonDynamicsSequenceState
            (cfgkat_transitions aut1)
            (cfgkat_initial aut2)
            (cfgkat_transitions aut2);
    cfgkat_labels :=
        CFGKATAutomatonDynamicsSequenceLabels
            (cfgkat_labels aut1)
            (cfgkat_initial aut2)
            (cfgkat_labels aut2);
    cfgkat_initial :=
        CFGKATAutomatonDynamicsSequence
            (cfgkat_initial aut1)
            (cfgkat_initial aut2);
|}.

Lemma cfgkat_automaton_sequence_preserves_wellformed
    (aut1 aut2: CFGKATAutomaton)
:
    CFGKATAutomatonWellFormed aut1 ->
    CFGKATAutomatonWellFormed aut2 ->
    cfgkat_automata_disjoint aut1 aut2 ->
    CFGKATAutomatonWellFormed (cfgkat_automaton_sequence aut1 aut2)
.
Proof.
    split; intros; simpl.
    - apply cfgkat_dynamics_sequence_state_preserves_functional; firstorder.
    - now apply cfgkat_automata_sequence_labels_functional.
    - apply cfgkat_dynamics_sequence_preserves_functional; firstorder.
Qed.

Lemma cfgkat_automaton_sequence_inject_right_complete
    (aut1 aut2: CFGKATAutomaton)
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut2))
    (i: IndicatorValue)
:
    CFGKATAutomatonAccepts aut2 d i (w, c) ->
    CFGKATAutomatonAccepts
        (cfgkat_automaton_sequence aut1 aut2)
        (CFGKATAutomatonDynamicsMorph inr d)
        i (w, c)
.
Proof.
    revert d i; dependent induction w; intros.
    - apply CFGKATAutomatonAcceptsBase; simpl.
      apply CFGKATAutomatonDynamicsMorphPause.
      now dependent destruction H.
    - dependent destruction H.
      eapply CFGKATAutomatonAcceptsStep; simpl.
      + apply CFGKATAutomatonDynamicsMorphNext; eauto.
      + now apply IHw.
Qed.

Lemma cfgkat_automaton_sequence_inject_left_complete
    (aut1 aut2: CFGKATAutomaton)
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut1))
    (i: IndicatorValue)
:
    GuardedLanguageWithContinuationsIndexedFamilySequence
        (CFGKATAutomatonAccepts aut1 d)
        (CFGKATAutomatonAccepts aut2 (cfgkat_initial aut2))
        i (w, c) ->
    CFGKATAutomatonAccepts
        (cfgkat_automaton_sequence aut1 aut2)
        (CFGKATAutomatonDynamicsSequence d (cfgkat_initial aut2))
        i (w, c)
.
Proof.
  intros.
  dependent destruction H.
  - revert d i j H H0; dependent induction H1; intros.
    + dependent destruction H.
      apply CFGKATAutomatonAcceptsBase.
      eapply CFGKATAutomatonDynamicsSequenceSkip; eauto.
      apply CFGKATAutomatonDynamicsMorphPause.
      now dependent destruction H0.
    + dependent destruction H.
      eapply CFGKATAutomatonAcceptsStep; simpl.
      * apply CFGKATAutomatonDynamicsSequenceEnterNext; eauto.
      * eapply cfgkat_automaton_accepts_invariant; eauto.
        eapply IHGuardedConcatenation; eauto.
    + dependent destruction H.
      dependent destruction H0.
      eapply CFGKATAutomatonAcceptsStep; simpl.
      * eapply CFGKATAutomatonDynamicsSequenceSkip; eauto.
        apply CFGKATAutomatonDynamicsMorphNext; eauto.
      * now apply cfgkat_automaton_sequence_inject_right_complete.
  - dependent induction H.
    + apply CFGKATAutomatonAcceptsBase; simpl.
      now apply CFGKATAutomatonDynamicsSequenceEnterBreak.
    + eapply CFGKATAutomatonAcceptsStep; simpl.
      * apply CFGKATAutomatonDynamicsSequenceEnterNext; eauto.
      * eapply cfgkat_automaton_accepts_invariant; eauto.
  - dependent induction H.
    + apply CFGKATAutomatonAcceptsBase; simpl.
      now apply CFGKATAutomatonDynamicsSequenceEnterReturn.
    + eapply CFGKATAutomatonAcceptsStep; simpl.
      * apply CFGKATAutomatonDynamicsSequenceEnterNext; eauto.
      * eapply cfgkat_automaton_accepts_invariant; eauto.
  - dependent induction H.
    + apply CFGKATAutomatonAcceptsBase; simpl.
      now apply CFGKATAutomatonDynamicsSequenceEnterJump.
    + eapply CFGKATAutomatonAcceptsStep; simpl.
      * apply CFGKATAutomatonDynamicsSequenceEnterNext; eauto.
      * eapply cfgkat_automaton_accepts_invariant; eauto.
Qed.

Lemma cfgkat_automaton_sequence_inject_right_sound
    (aut1 aut2: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut2))
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (i: IndicatorValue)
:
    CFGKATAutomatonAccepts
        (cfgkat_automaton_sequence aut1 aut2)
        (CFGKATAutomatonDynamicsMorph inr d)
        i (w, c) ->
    CFGKATAutomatonAccepts aut2 d i (w, c)
.
Proof.
    revert d c i; intros; dependent induction w.
    - apply CFGKATAutomatonAcceptsBase; simpl.
      simpl in H; now repeat dependent destruction H.
    - simpl in H; repeat dependent destruction H.
      eapply CFGKATAutomatonAcceptsStep; simpl; eauto.
Qed.

Lemma cfgkat_automaton_next_indexed_family_sequence
    (aut: CFGKATAutomaton)
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (s: cfgkat_states aut)
    (i i': IndicatorValue)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (L: GuardedLanguageWithContinuationsIndexedFamily)
    (a: Atom)
    (p: Action)
:
    d i a (CFGKATAutomatonNext p s i') ->
    GuardedLanguageWithContinuationsIndexedFamilySequence
        (CFGKATAutomatonAccepts aut (cfgkat_transitions aut s))
        L i' (w, c) ->
    GuardedLanguageWithContinuationsIndexedFamilySequence
      (CFGKATAutomatonAccepts aut d)
      L i (GuardedWordStep a p w, c)
.
Proof.
    intros.
    dependent destruction H0.
    - eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat; eauto.
      + eapply CFGKATAutomatonAcceptsStep; eauto.
      + now constructor.
    - eapply GuardedLanguageWithContinuationsIndexedFamilySequenceBreak.
      eapply CFGKATAutomatonAcceptsStep; eauto.
    - eapply GuardedLanguageWithContinuationsIndexedFamilySequenceReturn.
      eapply CFGKATAutomatonAcceptsStep; eauto.
    - eapply GuardedLanguageWithContinuationsIndexedFamilySequenceJump.
      eapply CFGKATAutomatonAcceptsStep; eauto.
Qed.

Lemma cfgkat_automaton_sequence_inject_left_sound
    (aut1 aut2: CFGKATAutomaton)
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (d1: CFGKATAutomatonDynamics (cfgkat_states aut1))
    (i: IndicatorValue)
:
    CFGKATAutomatonAccepts
        (cfgkat_automaton_sequence aut1 aut2)
        (CFGKATAutomatonDynamicsSequence d1 (cfgkat_initial aut2))
        i (w, c) ->
    GuardedLanguageWithContinuationsIndexedFamilySequence
        (CFGKATAutomatonAccepts aut1 d1)
        (CFGKATAutomatonAccepts aut2 (cfgkat_initial aut2))
        i (w, c)
.
Proof.
    intros.
    dependent induction w.
    - repeat dependent destruction H.
      + eapply GuardedLanguageWithContinuationsIndexedFamilySequenceBreak.
        now apply CFGKATAutomatonAcceptsBase.
      + eapply GuardedLanguageWithContinuationsIndexedFamilySequenceReturn.
        now apply CFGKATAutomatonAcceptsBase.
      + eapply GuardedLanguageWithContinuationsIndexedFamilySequenceJump.
        now apply CFGKATAutomatonAcceptsBase.
      + dependent destruction H0.
        eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat.
        * apply CFGKATAutomatonAcceptsBase; eauto.
        * apply CFGKATAutomatonAcceptsBase; eauto.
        * constructor.
    - simpl in H; repeat dependent destruction H.
      + eapply cfgkat_automaton_next_indexed_family_sequence; eauto.
      + dependent destruction H0.
        apply cfgkat_automaton_sequence_inject_right_sound in H1.
        eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat.
        * apply CFGKATAutomatonAcceptsBase, H.
        * eapply CFGKATAutomatonAcceptsStep; eauto.
        * constructor.
Qed.

Lemma cfgkat_automaton_sequence_correct_initial
    (aut1 aut2: CFGKATAutomaton)
:
    cfgkat_language_initial (cfgkat_automaton_sequence aut1 aut2) =
    GuardedLanguageWithContinuationsIndexedFamilySequence
        (cfgkat_language_initial aut1) (cfgkat_language_initial aut2)
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    unfold cfgkat_language_initial.
    split; intros.
    - now apply cfgkat_automaton_sequence_inject_left_sound.
    - now apply cfgkat_automaton_sequence_inject_left_complete.
Qed.

Lemma cfgkat_automaton_dynamics_sequence_extract
    {S1 S2: Type}
    (d1: CFGKATAutomatonDynamics S1)
    (d2: CFGKATAutomatonDynamics S2)
    (i: IndicatorValue)
    (a: Atom)
    (zeta: CFGKATAutomatonOutputs (S1 + S2))
:
    CFGKATAutomatonDynamicsSequence d1 d2 i a zeta ->
    exists zeta', d1 i a zeta'
.
Proof.
    intros; dependent destruction H;
    eexists; eauto.
Qed.

Lemma cfgkat_automaton_sequence_correct
    (aut1 aut2: CFGKATAutomaton)
:
    cfgkat_language (cfgkat_automaton_sequence aut1 aut2) =
    GuardedLanguageWithContinuationsLabeledFamilySequence
        (cfgkat_language aut1) (cfgkat_language aut2)
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    split; intro.
    - destruct le; simpl in *.
      + apply cfgkat_automaton_accepts_shift in H.
        destruct H as [a [zeta [? [? ?]]]].
        dependent destruction H1.
        * apply GuardedLanguageWithContinuationsLabeledFamilySequenceOffsetLeft; simpl.
          apply cfgkat_automaton_sequence_inject_left_sound.
          apply cfgkat_automaton_accepts_shift; repeat eexists; eauto.
        * apply GuardedLanguageWithContinuationsLabeledFamilySequenceOffsetRight; simpl.
          eapply cfgkat_automaton_sequence_inject_right_sound.
          apply cfgkat_automaton_accepts_shift; repeat eexists; eauto.
      + destruct u; simpl in H; constructor.
        unfold cfgkat_language.
        now erewrite <- cfgkat_automaton_sequence_correct_initial.
    - dependent destruction H; simpl in *.
      + now rewrite cfgkat_automaton_sequence_correct_initial.
      + eapply cfgkat_automaton_accepts_invariant.
        * eapply cfgkat_automaton_sequence_inject_left_complete; eauto.
        * intros; now constructor.
      + eapply cfgkat_automaton_accepts_invariant.
        * eapply cfgkat_automaton_sequence_inject_right_complete; eauto.
        * intros; now constructor.
Qed.

(* Loop composition of automata *)

Inductive CFGKATAutomatonDynamicsLoop
    {S: Type}
    (t: CFGKATTest)
    (d2: CFGKATAutomatonDynamics S)
    (d1: CFGKATAutomatonDynamics S)
:
    CFGKATAutomatonDynamics S
:=
| CFGKATAutomatonDynamicsLoopBreak:
    forall (i j: IndicatorValue) (a: Atom),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationBreak j)) ->
      CFGKATAutomatonDynamicsLoop t d2 d1 i a
        (CFGKATAutomatonPause (CFGKATContinuationBreak j))
| CFGKATAutomatonDynamicsLoopReturn:
    forall (i: IndicatorValue) (a: Atom),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationReturn)) ->
      CFGKATAutomatonDynamicsLoop t d2 d1 i a
        (CFGKATAutomatonPause (CFGKATContinuationReturn))
| CFGKATAutomatonDynamicsLoopJump:
    forall (i j: IndicatorValue) (a: Atom) (l: Label),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationJump j l)) ->
      CFGKATAutomatonDynamicsLoop t d2 d1 i a
        (CFGKATAutomatonPause (CFGKATContinuationJump j l))
| CFGKATAutomatonDynamicsLoopNext:
    forall (i j: IndicatorValue) (a: Atom) (p: Action) (s: S),
      d1 i a (CFGKATAutomatonNext p s j) ->
      CFGKATAutomatonDynamicsLoop t d2 d1 i a (CFGKATAutomatonNext p s j)
| CFGKATAutomatonDynamicsLoopStop:
    forall (i j: IndicatorValue) (a: Atom),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationAccept j)) ->
      ~t a ->
      CFGKATAutomatonDynamicsLoop t d2 d1 i a
        (CFGKATAutomatonPause (CFGKATContinuationAccept j))
| CFGKATAutomatonDynamicsLoopTighten:
    forall (i j: IndicatorValue) (a: Atom) (zeta: CFGKATAutomatonOutputs S),
      d1 i a (CFGKATAutomatonPause (CFGKATContinuationAccept j)) ->
      t a ->
      CFGKATAutomatonDynamicsLoop t d2 d2 j a zeta ->
      CFGKATAutomatonDynamicsLoop t d2 d1 i a zeta
.

Lemma cfgkat_dynamics_loop_preserves_functional
    {X: Type}
    (t: CFGKATTest)
    (d1: CFGKATAutomatonDynamics X)
    (d2: CFGKATAutomatonDynamics X)
:
    cfgkat_automaton_dynamics_functional d1 ->
    cfgkat_automaton_dynamics_functional d2 ->
    cfgkat_automaton_dynamics_functional (CFGKATAutomatonDynamicsLoop t d1 d2)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional at 3; intros.
    dependent induction H1.
    - dependent destruction H2; intuition;
      specialize (H0 _ _ _ _ H1 H2); inversion H0; now subst.
    - dependent destruction H2; intuition;
      specialize (H0 _ _ _ _ H1 H2); inversion H0.
    - dependent destruction H2; intuition;
      specialize (H0 _ _ _ _ H1 H2); inversion H0; now subst.
    - dependent destruction H2; intuition;
      specialize (H0 _ _ _ _ H1 H2); inversion H0; now subst.
    - dependent destruction H3; intuition;
      specialize (H0 _ _ _ _ H1 H3); inversion H0; now subst.
    - dependent destruction H4;
      specialize (H0 _ _ _ _ H1 H4); inversion H0; subst; intuition.
Qed.

Definition CFGKATAutomatonDynamicsLoopState
    {S: Type}
    (t: CFGKATTest)
    (d2: CFGKATAutomatonDynamics S)
    (d1: S -> CFGKATAutomatonDynamics S)
    (s: S)
:=
    CFGKATAutomatonDynamicsLoop t d2 (d1 s)
.

Lemma cfgkat_dynamics_loop_state_preserves_functional
    {X: Type}
    (t: CFGKATTest)
    (d1: X -> CFGKATAutomatonDynamics X)
    (d2: CFGKATAutomatonDynamics X)
:
    (forall s, cfgkat_automaton_dynamics_functional (d1 s)) ->
    cfgkat_automaton_dynamics_functional d2 ->
    forall s, cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsLoopState t d2 d1 s)
.
Proof.
  unfold cfgkat_automaton_dynamics_functional at 3; intros.
  eapply cfgkat_dynamics_loop_preserves_functional with (d2 := d1 s); eauto.
Qed.

Variant CFGKATAutomatonDynamicsLoopLabels
    {S: Type}
    (t: CFGKATTest)
    (d2: CFGKATAutomatonDynamics S)
    (d1: Label -> CFGKATAutomatonDynamics S)
:
    Label -> CFGKATAutomatonDynamics S
:=
| CFGKATAutomatonDynamicsLoopLabelsInner:
    forall l a i zeta,
      CFGKATAutomatonDynamicsLoop t d2 (d1 l) i a zeta ->
      CFGKATAutomatonDynamicsLoopLabels t d2 d1 l i a zeta
.

Lemma cfgkat_automata_loop_labels_functional
    (aut: CFGKATAutomaton)
    (t: CFGKATTest)
    (l: Label)
:
    CFGKATAutomatonWellFormed aut ->
    cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsLoopLabels
            t (cfgkat_initial aut) (cfgkat_labels aut) l)
.
Proof.
  unfold cfgkat_automaton_dynamics_functional; intros.
  dependent destruction H0.
  dependent destruction H1.
  eapply cfgkat_dynamics_loop_preserves_functional
    with (d1 := cfgkat_initial aut) (d2 := cfgkat_labels aut l);
  eauto; apply H.
Qed.

Definition cfgkat_automaton_loop
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
:
    CFGKATAutomaton
:= {|
    cfgkat_states := cfgkat_states aut;
    cfgkat_transitions :=
        CFGKATAutomatonDynamicsLoopState t
            (cfgkat_initial aut)
            (cfgkat_transitions aut);
    cfgkat_labels :=
        CFGKATAutomatonDynamicsLoopLabels t
            (cfgkat_initial aut)
            (cfgkat_labels aut);
    cfgkat_initial :=
        CFGKATAutomatonDynamicsLoop t
            (cfgkat_initial aut)
            CFGKATAutomatonDynamicsTrivial;
|}.

Lemma cfgkat_automaton_loop_preserves_wellformed
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
:
    CFGKATAutomatonWellFormed aut ->
    CFGKATAutomatonWellFormed (cfgkat_automaton_loop t aut)
.
Proof.
    split; intros; simpl.
    - apply cfgkat_dynamics_loop_state_preserves_functional; firstorder.
    - now apply cfgkat_automata_loop_labels_functional.
    - apply cfgkat_dynamics_loop_preserves_functional; try firstorder.
      apply cfgkat_automaton_dynamics_trivial_functional.
Qed.

Lemma cfgkat_automaton_loop_sound
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i: IndicatorValue)
:
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
        (CFGKATAutomatonDynamicsLoop t (cfgkat_initial aut) d)
        i (w, c) ->
    GuardedLanguageWithContinuationsIndexedFamilySequence
        (CFGKATAutomatonAccepts aut d)
        (GuardedLanguageWithContinuationsIndexedFamilyLoop
          t (CFGKATAutomatonAccepts aut (cfgkat_initial aut)))
        i (w, c)
.
Proof.
    revert d; dependent induction w; intros.
    - dependent destruction H.
      dependent induction H.
      + apply GuardedLanguageWithContinuationsIndexedFamilySequenceBreak.
        now apply CFGKATAutomatonAcceptsBase.
      + apply GuardedLanguageWithContinuationsIndexedFamilySequenceReturn.
        now apply CFGKATAutomatonAcceptsBase.
      + apply GuardedLanguageWithContinuationsIndexedFamilySequenceJump.
        now apply CFGKATAutomatonAcceptsBase.
      + eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat.
        * eapply CFGKATAutomatonAcceptsBase; eauto.
        * apply GuardedLanguageWithContinuationsIndexedFamilyLoopBase; eauto.
        * apply GuardedConcatenationBase.
      + specialize (IHCFGKATAutomatonDynamicsLoop aut c (cfgkat_initial aut)).
        repeat specialize (IHCFGKATAutomatonDynamicsLoop ltac:(reflexivity)).
        dependent destruction IHCFGKATAutomatonDynamicsLoop.
        * dependent destruction H4.
          dependent destruction H2.
          eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat;
          try constructor; eauto.
          eapply GuardedLanguageWithContinuationsIndexedFamilyLoopStep;
          eauto; now constructor.
        * dependent destruction H2.
          eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat;
          try constructor; eauto.
          eapply GuardedLanguageWithContinuationsIndexedFamilyLoopBreak;
          eauto; now constructor.
        * dependent destruction H2.
          eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat;
          try constructor; eauto.
          eapply GuardedLanguageWithContinuationsIndexedFamilyLoopReturn;
          eauto; now constructor.
        * dependent destruction H2.
          eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat;
          try constructor; eauto.
          eapply GuardedLanguageWithContinuationsIndexedFamilyLoopJump;
          eauto; now constructor.
    - dependent destruction H; simpl in H0.
      unfold CFGKATAutomatonDynamicsLoopState in H0.
      dependent induction H.
      + apply IHw in H0.
        dependent destruction H0.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat; eauto.
          -- eapply CFGKATAutomatonAcceptsStep; eauto.
          -- now apply GuardedConcatenationStep.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceBreak; eauto.
          eapply CFGKATAutomatonAcceptsStep; eauto.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceReturn; eauto.
          eapply CFGKATAutomatonAcceptsStep; eauto.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceJump; eauto.
          eapply CFGKATAutomatonAcceptsStep; eauto.
      + specialize (IHCFGKATAutomatonDynamicsLoop aut a0 IHw (cfgkat_initial aut) i' s).
        repeat specialize (IHCFGKATAutomatonDynamicsLoop ltac:(reflexivity)).
        specialize (IHCFGKATAutomatonDynamicsLoop H2).
        dependent destruction IHCFGKATAutomatonDynamicsLoop.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat;
          try constructor; eauto.
          eapply GuardedLanguageWithContinuationsIndexedFamilyLoopStep; eauto.
          dependent destruction H4; constructor.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat;
          repeat (constructor; eauto).
          eapply GuardedLanguageWithContinuationsIndexedFamilyLoopBreak;
          eauto; constructor.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat;
          repeat (constructor; eauto).
          eapply GuardedLanguageWithContinuationsIndexedFamilyLoopReturn;
          eauto; constructor.
        * eapply GuardedLanguageWithContinuationsIndexedFamilySequenceConcat;
          repeat (constructor; eauto).
          eapply GuardedLanguageWithContinuationsIndexedFamilyLoopJump;
          eauto; constructor.
Qed.

Lemma cfgkat_automaton_accepts_loop_merge
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
    (i j: IndicatorValue)
    (w x wx: GuardedWord)
    (c : CFGKATContinuation)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
:
    CFGKATAutomatonAccepts aut d i (w, CFGKATContinuationAccept j) ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
        (CFGKATAutomatonDynamicsLoop t
            (cfgkat_initial aut) CFGKATAutomatonDynamicsTrivial)
        j (x, c) ->
    GuardedConcatenation w x wx ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
        (CFGKATAutomatonDynamicsLoop t (cfgkat_initial aut) d) i (wx, c)
.
Proof.
    revert i j c d; dependent induction w; intros.
    - eapply cfgkat_automaton_merge_shift; intros.
      + erewrite <- guarded_concatenation_trivializes_left
          with (x := x) (wx := wx); eauto.
      + dependent destruction H1; constructor.
      + dependent destruction H.
        repeat dependent destruction H2.
        * now apply CFGKATAutomatonDynamicsLoopStop.
        * eapply CFGKATAutomatonDynamicsLoopTighten; eauto.
    - dependent destruction H1.
      dependent destruction H.
      econstructor.
      + constructor; eauto.
      + simpl; eapply IHw; eauto.
Qed.

Lemma cfgkat_automaton_accepts_loop_fold
    (t: CFGKATTest)
    (a: Atom)
    (aut: CFGKATAutomaton)
    (i: IndicatorValue)
    (w: GuardedWord)
    (c: CFGKATContinuation)
:
    t a ->
    GuardedWordStartsWith a w ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
      (CFGKATAutomatonDynamicsLoop t (cfgkat_initial aut) (cfgkat_initial aut))
      i (w, c) ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
      (CFGKATAutomatonDynamicsLoop t (cfgkat_initial aut)
         CFGKATAutomatonDynamicsTrivial) i (w, c)
.
Proof.
    intros.
    dependent destruction H0.
    - dependent destruction H1; constructor.
      eapply CFGKATAutomatonDynamicsLoopTighten; eauto.
      now constructor.
    - dependent destruction H1; econstructor; eauto.
      eapply CFGKATAutomatonDynamicsLoopTighten; eauto.
      now constructor.
Qed.

Lemma cfgkat_automaton_accepts_loop_break
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
    (i j: IndicatorValue)
    (w: GuardedWord)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
:
    CFGKATAutomatonAccepts aut d i
      (w, CFGKATContinuationBreak j) ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
      (CFGKATAutomatonDynamicsLoop t (cfgkat_initial aut) d) i
      (w, CFGKATContinuationBreak j)
.
Proof.
    intros.
    dependent induction H.
    - now repeat constructor.
    - econstructor.
      + constructor; eauto.
      + now apply IHCFGKATAutomatonAccepts.
Qed.

Lemma cfgkat_automaton_accepts_loop_return
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
    (i: IndicatorValue)
    (w: GuardedWord)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
:
    CFGKATAutomatonAccepts aut d i
      (w, CFGKATContinuationReturn) ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
      (CFGKATAutomatonDynamicsLoop t (cfgkat_initial aut) d) i
      (w, CFGKATContinuationReturn)
.
Proof.
    intros.
    dependent induction H.
    - now repeat constructor.
    - econstructor.
      + constructor; eauto.
      + now apply IHCFGKATAutomatonAccepts.
Qed.

Lemma cfgkat_automaton_accepts_loop_jump
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
    (i j: IndicatorValue)
    (l: Label)
    (w: GuardedWord)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
:
    CFGKATAutomatonAccepts aut d i
      (w, CFGKATContinuationJump j l) ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
      (CFGKATAutomatonDynamicsLoop t (cfgkat_initial aut) d) i
      (w, CFGKATContinuationJump j l)
.
Proof.
    intros.
    dependent induction H.
    - now repeat constructor.
    - econstructor.
      + constructor; eauto.
      + now apply IHCFGKATAutomatonAccepts.
Qed.

Lemma cfgkat_automaton_accepts_loop_first
    (aut: CFGKATAutomaton)
    (t: CFGKATTest)
    (i: IndicatorValue)
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (a: Atom)
:
    CFGKATAutomatonAccepts aut
      (CFGKATAutomatonDynamicsLoop t d CFGKATAutomatonDynamicsTrivial) i (w, c) ->
    GuardedWordStartsWith a w ->
    t a \/ (~t a /\ w = GuardedWordBase a)
.
Proof.
    intros.
    dependent destruction H.
    - dependent destruction H;
      try dependent destruction H.
      + dependent destruction H1; intuition.
      + dependent destruction H2; intuition.
    - repeat dependent destruction H.
      dependent destruction H3; intuition.
Qed.

Lemma cfgkat_automaton_accepts_loop_last
    (aut: CFGKATAutomaton)
    (t: CFGKATTest)
    (w x: GuardedWord)
    (i j: IndicatorValue)
    (c: CFGKATContinuation)
    (a: Atom)
    (d1 d2: CFGKATAutomatonDynamics (cfgkat_states aut))
:
    CFGKATAutomatonAccepts aut d1 i (w, CFGKATContinuationAccept j) ->
    GuardedConcatenation w (GuardedWordBase a) x ->
    ~ t a ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
        (CFGKATAutomatonDynamicsLoop t d2 d1) i (x, CFGKATContinuationAccept j)
.
Proof.
    intros.
    assert (w = x) by (eapply guarded_word_concat_last; eauto); subst.
    revert d2; dependent induction H; intros.
    - dependent destruction H0.
      now repeat constructor.
    - dependent destruction H0.
      econstructor.
      + constructor; eauto.
      + simpl.
        unfold CFGKATAutomatonDynamicsLoopState.
        apply IHCFGKATAutomatonAccepts; eauto.
Qed.

Lemma cfgkat_automaton_loop_complete
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
    (w: GuardedWord)
    (c: CFGKATContinuation)
    (i: IndicatorValue)
:
    GuardedLanguageWithContinuationsIndexedFamilyLoop
        t (CFGKATAutomatonAccepts aut (cfgkat_initial aut)) i (w, c) ->
    CFGKATAutomatonAccepts (cfgkat_automaton_loop t aut)
        (cfgkat_initial (cfgkat_automaton_loop t aut))
        i (w, c)
.
Proof.
    intros.
    induction H.
    - repeat constructor; auto.
    - eapply cfgkat_automaton_accepts_loop_fold; eauto.
      + eapply guarded_word_starts_with_lift; eauto.
      + eapply cfgkat_automaton_accepts_loop_merge; eauto.
    - eapply cfgkat_automaton_accepts_loop_fold; eauto.
      now apply cfgkat_automaton_accepts_loop_break.
    - eapply cfgkat_automaton_accepts_loop_fold; eauto.
      now apply cfgkat_automaton_accepts_loop_return.
    - eapply cfgkat_automaton_accepts_loop_fold; eauto.
      now apply cfgkat_automaton_accepts_loop_jump.
Qed.

Lemma cfgkat_automaton_loop_correct_initial
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
:
    cfgkat_language_initial (cfgkat_automaton_loop t aut) =
    GuardedLanguageWithContinuationsIndexedFamilyLoop
        t (cfgkat_language_initial aut)
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    unfold cfgkat_language_initial; simpl.
    split; intros.
    - apply cfgkat_automaton_loop_sound in H.
      repeat dependent destruction H.
      dependent destruction H1; auto.
    - now apply cfgkat_automaton_loop_complete.
Qed.

Lemma cfgkat_automaton_loop_correct
    (t: CFGKATTest)
    (aut: CFGKATAutomaton)
:
    cfgkat_language (cfgkat_automaton_loop t aut) =
    GuardedLanguageWithContinuationsLabeledFamilyLoop t (cfgkat_language aut)
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    destruct le; simpl.
    - split; intros.
      + eapply GuardedLanguageWithContinuationsLabeledFamilyLoopOffset; simpl.
        eapply cfgkat_automaton_loop_sound.
        eapply cfgkat_automaton_accepts_invariant; eauto; intros.
        now dependent destruction H0.
      + repeat dependent destruction H.
        * eapply cfgkat_automaton_accepts_invariant; intros.
          -- eapply cfgkat_automaton_accepts_loop_merge with (aut := aut); eauto.
             now apply cfgkat_automaton_loop_complete.
          -- now constructor.
        * eapply cfgkat_automaton_accepts_invariant; intros.
          -- apply cfgkat_automaton_accepts_loop_break with (aut := aut); eauto.
          -- now constructor.
        * eapply cfgkat_automaton_accepts_invariant; intros.
          -- apply cfgkat_automaton_accepts_loop_return with (aut := aut); eauto.
          -- now constructor.
        * eapply cfgkat_automaton_accepts_invariant; intros.
          -- apply cfgkat_automaton_accepts_loop_jump with (aut := aut); eauto.
          -- now constructor.
    - destruct u; simpl; split; intros.
      + constructor.
        unfold cfgkat_language.
        now rewrite <- cfgkat_automaton_loop_correct_initial.
      + dependent destruction H.
        now rewrite cfgkat_automaton_loop_correct_initial.
Qed.

(* Grounding of CF-GKAT automata *)

Variant CFGKATAutomatonDynamicsGround
    {S: Type}
    (d: CFGKATAutomatonDynamics S)
:
    CFGKATAutomatonDynamics S
:=
| CFGKATAutomatonDynamicsGroundAccept:
    forall (i j: IndicatorValue) (a: Atom),
      d i a (CFGKATAutomatonPause (CFGKATContinuationAccept j)) ->
      CFGKATAutomatonDynamicsGround d i a
        (CFGKATAutomatonPause (CFGKATContinuationAccept j))
| CFGKATAutomatonDynamicsGroundBreak:
    forall (i j: IndicatorValue) (a: Atom),
      d i a (CFGKATAutomatonPause (CFGKATContinuationBreak j)) ->
      CFGKATAutomatonDynamicsGround d i a
        (CFGKATAutomatonPause (CFGKATContinuationAccept j))
| CFGKATAutomatonDynamicsGroundReturn:
    forall (i: IndicatorValue) (a: Atom),
      d i a (CFGKATAutomatonPause (CFGKATContinuationReturn)) ->
      CFGKATAutomatonDynamicsGround d i a
        (CFGKATAutomatonPause (CFGKATContinuationReturn))
| CFGKATAutomatonDynamicsGroundJump:
    forall (i j: IndicatorValue) (a: Atom) (l: Label),
      d i a (CFGKATAutomatonPause (CFGKATContinuationJump j l)) ->
      CFGKATAutomatonDynamicsGround d i a
        (CFGKATAutomatonPause (CFGKATContinuationJump j l))
| CFGKATAutomatonDynamicsGroundNext:
    forall (i j: IndicatorValue) (a: Atom) (p: Action) (s: S),
      d i a (CFGKATAutomatonNext p s j) ->
      CFGKATAutomatonDynamicsGround d i a
        (CFGKATAutomatonNext p s j)
.

Lemma cfgkat_dynamics_ground_preserves_functional
    {X: Type}
    (d: CFGKATAutomatonDynamics X)
:
    cfgkat_automaton_dynamics_functional d ->
    cfgkat_automaton_dynamics_functional (CFGKATAutomatonDynamicsGround d)
.
Proof.
    unfold cfgkat_automaton_dynamics_functional at 2; intros.
    dependent destruction H0;
    dependent destruction H1; intuition;
    specialize (H _ _ _ _ H0 H1); now inversion H.
Qed.


Definition CFGKATAutomatonDynamicsGroundLift
    {S T: Type}
    (d: T -> CFGKATAutomatonDynamics S)
    (t: T)
:
    CFGKATAutomatonDynamics S
:=
    CFGKATAutomatonDynamicsGround (d t)
.

Lemma cfgkat_dynamics_ground_lift_preserves_functional
    {S T: Type}
    (d: T -> CFGKATAutomatonDynamics S)
:
    (forall t, cfgkat_automaton_dynamics_functional (d t)) ->
    forall t, cfgkat_automaton_dynamics_functional
        (CFGKATAutomatonDynamicsGroundLift d t)
.
Proof.
  unfold cfgkat_automaton_dynamics_functional at 2; intros.
  eapply cfgkat_dynamics_ground_preserves_functional with (d := d t); eauto.
Qed.

Definition cfgkat_automaton_ground
    (aut: CFGKATAutomaton)
:
    CFGKATAutomaton
:= {|
    cfgkat_states := cfgkat_states aut;
    cfgkat_transitions :=
        CFGKATAutomatonDynamicsGroundLift (cfgkat_transitions aut);
    cfgkat_labels :=
        CFGKATAutomatonDynamicsGroundLift (cfgkat_labels aut);
    cfgkat_initial :=
        CFGKATAutomatonDynamicsGround (cfgkat_initial aut);
|}.

Lemma cfgkat_automaton_ground_preserves_wellformed
    (aut: CFGKATAutomaton)
:
    CFGKATAutomatonWellFormed aut ->
    CFGKATAutomatonWellFormed (cfgkat_automaton_ground aut)
.
Proof.
    split; intros; simpl.
    - apply cfgkat_dynamics_ground_lift_preserves_functional; firstorder.
    - apply cfgkat_dynamics_ground_lift_preserves_functional; firstorder.
    - apply cfgkat_dynamics_ground_preserves_functional; firstorder.
Qed.

Lemma cfgkat_automaton_ground_sound
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i: IndicatorValue)
    (w: GuardedWord)
    (c: CFGKATContinuation)
:
    CFGKATAutomatonAccepts
      (cfgkat_automaton_ground aut)
      (CFGKATAutomatonDynamicsGround d) i (w, c) ->
    GuardedLanguageWithContinuationsIndexedFamilyGround
        (CFGKATAutomatonAccepts aut d) i (w, c)
.
Proof.
    revert d i c; dependent induction w; intros.
    - repeat dependent destruction H;
      now repeat constructor.
    - dependent destruction H.
      apply IHw in H0.
      dependent destruction H.
      dependent destruction H0;
      try now (repeat econstructor; eauto).
Qed.

Lemma cfgkat_automaton_ground_complete
    (aut: CFGKATAutomaton)
    (d: CFGKATAutomatonDynamics (cfgkat_states aut))
    (i: IndicatorValue)
    (w: GuardedWord)
    (c: CFGKATContinuation)
:
    GuardedLanguageWithContinuationsIndexedFamilyGround
        (CFGKATAutomatonAccepts aut d) i (w, c) ->
    CFGKATAutomatonAccepts
      (cfgkat_automaton_ground aut)
      (CFGKATAutomatonDynamicsGround d) i (w, c)
.
Proof.
    revert d i c; intros;
    dependent destruction H;
    dependent induction H;
    now (repeat econstructor; eauto; firstorder).
Qed.

Lemma cfgkat_automaton_ground_correct_initial
    (aut: CFGKATAutomaton)
:
    cfgkat_language_initial (cfgkat_automaton_ground aut) =
    GuardedLanguageWithContinuationsIndexedFamilyGround
        (cfgkat_language_initial aut)
.
Proof.
    guarded_language_with_continuations_indexed_family_extensionality.
    unfold cfgkat_language_initial; simpl; split; intros.
    - now apply cfgkat_automaton_ground_sound.
    - now apply cfgkat_automaton_ground_complete.
Qed.

Lemma cfgkat_automaton_ground_correct
    (aut: CFGKATAutomaton)
:
    cfgkat_language (cfgkat_automaton_ground aut) =
    GuardedLanguageWithContinuationsLabeledFamilyGround (cfgkat_language aut)
.
Proof.
    guarded_language_with_continuations_labeled_family_extensionality.
    destruct le; simpl.
    - split; intros.
      + constructor.
        now apply cfgkat_automaton_ground_sound.
      + dependent destruction H.
        now apply cfgkat_automaton_ground_complete.
    - destruct u; split; intros.
      + constructor; unfold cfgkat_language.
        now erewrite <- cfgkat_automaton_ground_correct_initial.
      + dependent destruction H.
        now rewrite cfgkat_automaton_ground_correct_initial.
Qed.

(* Thompson construction *)

Fixpoint thompson_construction (e: CFGKATExpression) : CFGKATAutomaton :=
    match e with
    | CFGKATAssert t =>
      cfgkat_automaton_assert t
    | CFGKATEquals i =>
      cfgkat_automaton_equals i
    | CFGKATAct p =>
      cfgkat_automaton_act p
    | CFGKATAssign i =>
      cfgkat_automaton_assign i
    | CFGKATBreak =>
      cfgkat_automaton_break
    | CFGKATReturn =>
      cfgkat_automaton_return
    | CFGKATGoto l =>
      cfgkat_automaton_goto l
    | CFGKATLabel l =>
      cfgkat_automaton_label l
    | CFGKATChoice t e1 e2 =>
      cfgkat_automaton_choice t
        (thompson_construction e1)
        (thompson_construction e2)
    | CFGKATSequence e1 e2 =>
      cfgkat_automaton_sequence
        (thompson_construction e1)
        (thompson_construction e2)
    | CFGKATLoop t e =>
      cfgkat_automaton_ground (
        cfgkat_automaton_loop t (thompson_construction e)
      )
    end
.

Theorem thompson_construction_correct (e: CFGKATExpression):
    cfgkat_language (thompson_construction e) =
    cfgkat_expression_semantics e
.
Proof.
    induction e; simpl; intros.
    - apply cfgkat_automaton_assert_correct.
    - apply cfgkat_automaton_equals_correct.
    - apply cfgkat_automaton_act_correct.
    - apply cfgkat_automaton_assign_correct.
    - apply cfgkat_automaton_break_correct.
    - apply cfgkat_automaton_return_correct.
    - apply cfgkat_automaton_goto_correct.
    - apply cfgkat_automaton_label_correct.
    - now rewrite cfgkat_automaton_choice_correct, IHe1, IHe2.
    - now rewrite cfgkat_automaton_sequence_correct, IHe1, IHe2.
    - now rewrite cfgkat_automaton_ground_correct, cfgkat_automaton_loop_correct, IHe.
Qed.

Check thompson_construction_correct.
Print Assumptions thompson_construction_correct.

Lemma cfgkat_expression_label_thompson (e: CFGKATExpression) (l: Label):
    cfgkat_automaton_has_label (thompson_construction e) l ->
    CFGKATExpressionLabelFor l e
.
Proof.
    induction e; unfold cfgkat_automaton_has_label; intros;
    destruct H as [i' [a' [zeta ?]]]; simpl in H; dependent destruction H.
    - constructor.
    - apply CFGKATExpressionLabelForChoiceLeft, IHe1.
      dependent destruction H;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
    - apply CFGKATExpressionLabelForChoiceRight, IHe2.
      dependent destruction H;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
    - dependent destruction H;
      apply CFGKATExpressionLabelForSequenceLeft, IHe1;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
    - dependent destruction H;
      apply CFGKATExpressionLabelForSequenceRight, IHe2;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
    - dependent destruction H; dependent destruction H;
      apply CFGKATExpressionLabelForLoop, IHe;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
    - dependent destruction H; dependent destruction H;
      apply CFGKATExpressionLabelForLoop, IHe;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
    - dependent destruction H; dependent destruction H;
      apply CFGKATExpressionLabelForLoop, IHe;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
    - dependent destruction H; dependent destruction H;
      apply CFGKATExpressionLabelForLoop, IHe;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
    - dependent destruction H; dependent destruction H;
      apply CFGKATExpressionLabelForLoop, IHe;
      unfold cfgkat_automaton_has_label; repeat eexists; eauto.
Qed.

Lemma cfgkat_expression_thompson_disjoint (e1 e2: CFGKATExpression):
    cfgkat_labels_disjoint e1 e2 ->
    cfgkat_automata_disjoint
      (thompson_construction e1)
      (thompson_construction e2)
.
Proof.
    unfold cfgkat_labels_disjoint, cfgkat_automata_disjoint; intros.
    specialize (H l); destruct H.
    - left; intro; apply H.
      now apply cfgkat_expression_label_thompson.
    - right; intro; apply H.
      now apply cfgkat_expression_label_thompson.
Qed.

Lemma thompson_construction_wellformed (e: CFGKATExpression):
    CFGKATExpressionWellFormed e ->
    CFGKATAutomatonWellFormed (thompson_construction e)
.
Proof.
    intros; dependent induction H; simpl; intros.
    - apply cfgkat_automaton_assert_wellformed.
    - apply cfgkat_automaton_equals_wellformed.
    - apply cfgkat_automaton_act_wellformed.
    - apply cfgkat_automaton_assign_wellformed.
    - apply cfgkat_automaton_break_wellformed.
    - apply cfgkat_automaton_return_wellformed.
    - apply cfgkat_automaton_goto_wellformed.
    - apply cfgkat_automaton_label_wellformed.
    - apply cfgkat_automaton_choice_preserves_wellformed; auto.
      now apply cfgkat_expression_thompson_disjoint.
    - apply cfgkat_automaton_sequence_preserves_wellformed; auto.
      now apply cfgkat_expression_thompson_disjoint.
    - apply cfgkat_automaton_ground_preserves_wellformed; auto.
      apply cfgkat_automaton_loop_preserves_wellformed; auto.
Qed.

Check thompson_construction_wellformed.
Print Assumptions thompson_construction_wellformed.
