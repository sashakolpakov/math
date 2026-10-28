import OAI.Algorithms.SubexponentialSAT.Computation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

structure LocatedCfg (machine : PrimitiveMachine) where
  config : machine.Cfg
  position : Fin machine.tapeCount → ℤ
  lower : Fin machine.tapeCount → ℤ
  upper : Fin machine.tapeCount → ℤ

def locatedInit (machine : PrimitiveMachine) (input : List Bool) : LocatedCfg machine where
  config := machine.init input
  position _ := 0
  lower _ := 0
  upper i := if i = machine.inputTape then Int.ofNat (input.length - 1) else 0

def headDisplacement : Turing.TM0.Stmt (Option Bool) → ℤ
  | .move .left => -1
  | .move .right => 1
  | .write _ => 0

theorem headDisplacement_bounds (action : Turing.TM0.Stmt (Option Bool)) :
    -1 ≤ headDisplacement action ∧ headDisplacement action ≤ 1 := by
  cases action with
  | move direction => cases direction <;> decide
  | write symbol =>
      change (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1
      decide

def LocatedCfg.monitor {machine : PrimitiveMachine} (c : LocatedCfg machine)
    (config : machine.Cfg) : LocatedCfg machine :=
  Sum.elim
    (fun _ => { c with config })
    (fun q =>
      Sum.elim
        (fun _ => { c with config })
        (fun targetAction =>
          let action := targetAction.2
          let i := machine.scan q
          let position := c.position i + headDisplacement action
          { config
            position := Function.update c.position i position
            lower := Function.update c.lower i (min (c.lower i) position)
            upper := Function.update c.upper i (max (c.upper i) position) })
        (machine.transition q (c.config.tapes (machine.scan q)).head))
    c.config.state

def locatedStep (machine : PrimitiveMachine) (c : LocatedCfg machine) :
    Option (LocatedCfg machine) :=
  (machine.step c.config).map c.monitor

def visitedSpace {machine : PrimitiveMachine} (c : LocatedCfg machine) : ℕ :=
  ∑ i, (c.upper i - c.lower i + 1).toNat

@[simp] theorem LocatedCfg.monitor_config {machine : PrimitiveMachine}
    (c : LocatedCfg machine) (config : machine.Cfg) :
    (c.monitor config).config = config := by
  cases hs : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hs]
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hs, ht]
      | inr result =>
          obtain ⟨next, action⟩ := result
          simp [LocatedCfg.monitor, hs, ht]

theorem locatedStep_erase (machine : PrimitiveMachine) (c : LocatedCfg machine) :
    (locatedStep machine c).map LocatedCfg.config = machine.step c.config := by
  simp only [locatedStep, Option.map_map]
  cases machine.step c.config <;> simp

theorem locatedStep_config {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (h : locatedStep machine c = some d) : machine.step c.config = some d.config := by
  rw [← locatedStep_erase machine c, h]
  rfl

theorem locatedStep_position_action {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {q next : Fin machine.stateCount}
    {action : Turing.TM0.Stmt (Option Bool)}
    (hs : locatedStep machine c = some d) (hq : c.config.state = .inr q)
    (ha : machine.transition q (c.config.tapes (machine.scan q)).head = .inr (next, action)) :
    d.position = Function.update c.position (machine.scan q)
      (c.position (machine.scan q) + headDisplacement action) := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  simp [LocatedCfg.monitor, hq, ha]

theorem locatedStep_position_halt {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {q : Fin machine.stateCount} {answer : Bool}
    (hs : locatedStep machine c = some d) (hq : c.config.state = .inr q)
    (ha : machine.transition q (c.config.tapes (machine.scan q)).head = .inl answer) :
    d.position = c.position := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  simp [LocatedCfg.monitor, hq, ha]

theorem locatedStep_position_bounds {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (i : Fin machine.tapeCount) :
    c.position i - 1 ≤ d.position i ∧ d.position i ≤ c.position i + 1 := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases hs : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hs]
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hs, ht]
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hs, ht, Function.update_self]
            have h := headDisplacement_bounds action
            omega
          · simp [LocatedCfg.monitor, hs, ht, Function.update_of_ne hi]

theorem locatedTrace_position_bounds {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) (i : Fin machine.tapeCount) :
    c.position i - (steps : ℤ) ≤ d.position i ∧
      d.position i ≤ c.position i + (steps : ℤ) := by
  induction tr with
  | refl => simp
  | cons hs _ ih =>
      have h := locatedStep_position_bounds hs i
      omega

theorem locatedTrace_erase {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (h : Computation.Trace (locatedStep machine) steps c d) :
    Computation.Trace machine.step steps c.config d.config := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih => exact .cons (locatedStep_config hs) ih

theorem locatedTrace_lift {machine : PrimitiveMachine} {c : LocatedCfg machine}
    {config : machine.Cfg} {steps : ℕ}
    (h : Computation.Trace machine.step steps c.config config) :
    ∃ d : LocatedCfg machine,
      Computation.Trace (locatedStep machine) steps c d ∧ d.config = config := by
  generalize hc : c.config = start at h
  induction h generalizing c with
  | refl => exact ⟨c, .refl c, hc⟩
  | @cons steps start next final hs _ ih =>
      have hstep : locatedStep machine c = some (c.monitor next) := by
        simp [locatedStep, hc, hs]
      obtain ⟨d, hd, hcfg⟩ := ih (c := c.monitor next) (c.monitor_config next)
      exact ⟨d, .cons hstep hd, hcfg⟩

theorem locatedStep_encloses {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d)
    (h : ∀ i, c.lower i ≤ c.position i ∧ c.position i ≤ c.upper i) :
    ∀ i, d.lower i ≤ d.position i ∧ d.position i ≤ d.upper i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  intro i
  cases hstate : c.config.state with
  | inl answer => simpa [LocatedCfg.monitor, hstate] using h i
  | inr q =>
      cases htransition : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simpa [LocatedCfg.monitor, hstate, htransition] using h i
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hstate, htransition, Function.update_self]
          · simpa [LocatedCfg.monitor, hstate, htransition, Function.update_of_ne hi] using h i

theorem locatedStep_expands {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (i : Fin machine.tapeCount) :
    d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases hstate : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hstate]
  | inr q =>
      cases htransition : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hstate, htransition]
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hstate, htransition, Function.update_self]
          · simp [LocatedCfg.monitor, hstate, htransition, Function.update_of_ne hi]

theorem locatedStep_envelope {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ i, lower i ≤ d.position i ∧ d.position i ≤ upper i) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  intro i
  have hc' := hc i
  have hp' := hp i
  cases hs : c.config.state with
  | inl answer => simpa [LocatedCfg.monitor, hs] using hc'
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simpa [LocatedCfg.monitor, hs, ht] using hc'
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hs, ht, Function.update_self] at hp' ⊢
            exact ⟨⟨hc'.1, hp'.1⟩, hc'.2, hp'.2⟩
          · simpa [LocatedCfg.monitor, hs, ht, Function.update_of_ne hi] using hc'

theorem locatedTrace_encloses {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (tr : Computation.Trace (locatedStep machine) steps c d)
    (h : ∀ i, c.lower i ≤ c.position i ∧ c.position i ≤ c.upper i) :
    ∀ i, d.lower i ≤ d.position i ∧ d.position i ≤ d.upper i := by
  induction tr with
  | refl => exact h
  | cons hs _ ih => exact ih (locatedStep_encloses hs h)

theorem locatedTrace_init_encloses {machine : PrimitiveMachine} {input : List Bool}
    {d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps (locatedInit machine input) d) :
    ∀ i, d.lower i ≤ d.position i ∧ d.position i ≤ d.upper i := by
  apply locatedTrace_encloses tr
  intro i
  simp only [locatedInit, Int.ofNat_eq_natCast]
  split_ifs <;> omega

theorem locatedTrace_expands {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (tr : Computation.Trace (locatedStep machine) steps c d)
    (i : Fin machine.tapeCount) :
    d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i := by
  induction tr with
  | refl => exact ⟨le_rfl, le_rfl⟩
  | cons hs _ ih =>
      have h := locatedStep_expands hs i
      exact ⟨ih.1.trans h.1, h.2.trans ih.2⟩

theorem visitedSpace_mono {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (h : ∀ i, d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i) :
    visitedSpace c ≤ visitedSpace d := by
  apply Finset.sum_le_sum
  intro i _
  apply Int.toNat_le_toNat
  have hi := h i
  omega

theorem locatedTrace_visitedSpace_mono {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) :
    visitedSpace c ≤ visitedSpace d :=
  visitedSpace_mono (locatedTrace_expands tr)

theorem trace_prefix_exists {α : Type*} {step : α → Option α}
    {a b : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps a b) (hle : prefixSteps ≤ steps) :
    ∃ intermediate, Computation.Trace step prefixSteps a intermediate := by
  induction tr generalizing prefixSteps with
  | refl a =>
      have hp : prefixSteps = 0 := by omega
      subst prefixSteps
      exact ⟨a, .refl a⟩
  | @cons steps a next final hs ht ih =>
      cases prefixSteps with
      | zero => exact ⟨a, .refl a⟩
      | succ prefixSteps =>
          obtain ⟨intermediate, hp⟩ := ih (prefixSteps := prefixSteps) (by omega)
          exact ⟨intermediate, .cons hs hp⟩

theorem trace_same_length_unique {α : Type*} {step : α → Option α}
    {a b c : α} {steps : ℕ}
    (hb : Computation.Trace step steps a b)
    (hc : Computation.Trace step steps a c) : b = c :=
  Option.some.inj (hb.iterate.symm.trans hc.iterate)

theorem trace_suffix {α : Type*} {step : α → Option α}
    {c d intermediate : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps c d)
    (hp : Computation.Trace step prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) :
    Computation.Trace step (steps - prefixSteps) intermediate d := by
  apply Computation.Trace.of_iterate
  have h := tr.iterate
  conv_lhs at h => rw [← Nat.sub_add_cancel hle]
  rw [Function.iterate_add_apply, hp.iterate] at h
  exact h

theorem trace_prefix_bound_trans {α : Type*} {step : α → Option α}
    {a b : α} {firstSteps secondSteps : ℕ} {P : α → Prop}
    (first : Computation.Trace step firstSteps a b)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ secondSteps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps + secondSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle htrace
  by_cases hprefix : prefixSteps ≤ firstSteps
  · exact hfirst prefixSteps intermediate hprefix htrace
  · exact hsecond (prefixSteps - firstSteps) intermediate (by omega)
      (trace_suffix htrace first (by omega))

theorem trace_prefix_bound_cons {α : Type*} {step : α → Option α}
    {a b : α} {steps : ℕ} {P : α → Prop}
    (hs : step a = some b) (ha : P a)
    (htail : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle hp
  cases hp with
  | refl => exact ha
  | cons hs' ht =>
      have heq := Option.some.inj (hs.symm.trans hs')
      subst b
      exact htail _ _ (by omega) ht

theorem locatedTrace_prefix_space {machine : PrimitiveMachine}
    {c d intermediate : LocatedCfg machine} {steps prefixSteps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d)
    (hp : Computation.Trace (locatedStep machine) prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) : visitedSpace intermediate ≤ visitedSpace d :=
  locatedTrace_visitedSpace_mono (trace_suffix tr hp hle)

theorem locatedTrace_envelope {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (tr : Computation.Trace (locatedStep machine) steps c d)
    (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace (locatedStep machine) prefixSteps c intermediate →
      ∀ i, lower i ≤ intermediate.position i ∧ intermediate.position i ≤ upper i) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  induction tr with
  | refl => exact hc
  | @cons steps c next final hs ht ih =>
      apply ih
      · exact locatedStep_envelope hs lower upper hc
          (hp 1 next (by omega) (.cons hs (.refl next)))
      · intro prefixSteps intermediate hle htr
        exact hp (prefixSteps + 1) intermediate (by omega) (.cons hs htr)

theorem locatedTrace_envelope_of_margin {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps budget : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) (ht : steps ≤ budget)
    (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ i, lower i + (budget : ℤ) ≤ c.position i ∧
      c.position i ≤ upper i - (budget : ℤ)) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  apply locatedTrace_envelope tr lower upper hc
  intro prefixSteps intermediate hle htr i
  have hmove := locatedTrace_position_bounds htr i
  have hstart := hp i
  omega

theorem visitedSpace_le_of_envelope {machine : PrimitiveMachine}
    (c : LocatedCfg machine) (lower upper : Fin machine.tapeCount → ℤ)
    (h : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i) :
    visitedSpace c ≤ ∑ i, (upper i - lower i + 1).toNat := by
  apply Finset.sum_le_sum
  intro i _
  apply Int.toNat_le_toNat
  have hi := h i
  omega

/-- Useful for polynomial-time preprocessing fragments only: substituting the
full exponential counting time here would not give polynomial space. -/
theorem locatedTrace_space_le_of_length {machine : PrimitiveMachine} {input : List Bool}
    {d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps (locatedInit machine input) d) :
    visitedSpace d ≤ machine.tapeCount * (input.length + 2 * steps + 1) := by
  have hinitial : ∀ i,
      -(steps : ℤ) ≤ (locatedInit machine input).lower i ∧
      (locatedInit machine input).upper i ≤ (input.length : ℤ) + steps := by
    intro i
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  have hpositions : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace (locatedStep machine) prefixSteps
        (locatedInit machine input) intermediate →
      ∀ i, -(steps : ℤ) ≤ intermediate.position i ∧
        intermediate.position i ≤ (input.length : ℤ) + steps := by
    intro prefixSteps intermediate hle htr i
    have h := locatedTrace_position_bounds htr i
    simp only [locatedInit] at h
    omega
  have h := locatedTrace_envelope tr (fun _ => -(steps : ℤ))
    (fun _ => (input.length : ℤ) + steps) hinitial hpositions
  apply (visitedSpace_le_of_envelope d _ _ h).trans
  have hwidth : ((input.length : ℤ) + steps - -(steps : ℤ) + 1).toNat =
      input.length + 2 * steps + 1 := by omega
  simp only [hwidth, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact le_rfl


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
