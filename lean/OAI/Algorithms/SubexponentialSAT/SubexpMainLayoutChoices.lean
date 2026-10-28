import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutProgram
import OAI.Algorithms.SubexponentialSAT.SubexpMainPackingCanonical
import OAI.Algorithms.SubexponentialSAT.SubexpMainLocalBasis
import OAI.Algorithms.SubexponentialSAT.SubexpMainCoefficientsSelected
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# Actual construction of the retained layout choices

This module composes the fixed prefix, coefficient, scalar-cache, packing
and local-basis programs. Every later input is identified with a preceding
program's physical output.
-/

namespace SubexponentialSAT.SubexpMainLayoutChoices

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation master ordinary)

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Ordinary254 retains the actual duplicate coefficient stream. -/
def Workspace {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : Prop :=
  ∀ i : Fin 640, i.val ≠ 254 → a.stacks (ordinary alloc (i.castAdd 32)) = []

private def scalarIndex (i : Fin 7) : Fin 32 := ⟨21 + i.val, by omega⟩

/-- The actual entry to the local-basis wrapper, before its binary-R
conversion and erasure of the old output word. -/
structure EntryFacts {er es : ℕ} (alloc : Allocation es) (a entry : MainState er es) : Prop where
  workspace : Workspace alloc entry
  persistent : ∀ i, entry.stacks (persistent es i) = a.stacks (persistent es i)
  oldBasisOutput : entry.stacks (master alloc 14) = a.stacks (master alloc 14)

theorem EntryFacts.oldBasisOutput_empty {er es : ℕ} {alloc : Allocation es}
    {a entry : MainState er es} (h : EntryFacts alloc a entry)
    (hzero : ∀ i : Fin 672, a.stacks (ordinary alloc i) = []) :
    entry.stacks (master alloc 14) = [] := h.oldBasisOutput.trans (hzero 654)

private theorem factors_master14 {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {scopes tables : List (List Bool)}
    (h : SubexpMainLayout.Factors.Result alloc a b scopes tables) :
    b.stacks (master alloc 14) = a.stacks (master alloc 14) := by
  have hhigh (j : Fin 7) : SubexpMainLayout.Factors.highPort alloc j ≠ master alloc 14 := by
    intro he
    have hv := congrArg Fin.val he
    have hw := alloc.enough.trans alloc.within
    fin_cases j <;> norm_num [SubexpMainLayout.Factors.highPort, persistent,
      SubexpLayoutPorts.scopes, SubexpLayoutPorts.tables, SubexpLayoutPorts.master, ordinary] at hv <;> omega
  apply h.frame
  rintro ⟨i, hi⟩
  by_cases hm : 35 ≤ (SubexpMainLayout.Factors.permutation i).val ∧
      (SubexpMainLayout.Factors.permutation i).val < 42
  · exact hhigh ⟨(SubexpMainLayout.Factors.permutation i).val - 35, by omega⟩
      (by simpa only [SubexpMainLayout.Factors.stackMap, SubexpMainLayout.Factors.baseMap,
        dite_eq_left hm] using hi)
  · have hv := congrArg Fin.val hi
    have hb := (SubexpMainLayout.Factors.permutation i).isLt
    simp only [SubexpMainLayout.Factors.stackMap, SubexpMainLayout.Factors.baseMap,
      dite_eq_right hm, ordinary, SubexpLayoutPorts.master_val] at hv
    norm_num at hv
    omega

private theorem prefix_transport {er es r Q Δ D : ℕ} {alloc : Allocation es}
    {a b c : MainState er es} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {first : MulticolorTypes.Word r Q} {tail : List (MulticolorTypes.Word r Q)}
    {tables : List (List Bool)}
    (h : SubexpMainLayoutPrefix.Result alloc a b r Q Δ D scopes hd first tail tables)
    (hm : ∀ i : Fin 32, i.val ≤ 8 ∨ i = 10 →
      c.stacks (master alloc i) = b.stacks (master alloc i))
    (hp : ∀ i, c.stacks (persistent es i) = b.stacks (persistent es i))
    (hc : ∀ i, c.regs (controlRegister er i) = b.regs (controlRegister er i)) :
    SubexpMainLayoutPrefix.Result alloc a c r Q Δ D scopes hd first tail tables := by
  refine ⟨h.wordOrder, (hm 0 (by decide)).trans h.scopeBytes,
    (hm 1 (by decide)).trans h.tableBytes, (hm 2 (by decide)).trans h.assignment,
    (hm 3 (by decide)).trans h.alphabet, ?_, ?_,
    (hm 10 (by decide)).trans h.universal, ?_, ?_⟩
  · rw [hm 4 (by decide)]
    exact h.width
  · intro i
    exact (hm (SubexpMainAssignment.headerIndex i) (by
      left
      dsimp [SubexpMainAssignment.headerIndex]
      omega)).trans (h.headers i)
  · intro i
    exact (hp i).trans (h.persistent i)
  · intro i
    exact (hc i).trans (h.controls i)

private theorem coefficient_master {er es p r Q R : ℕ} [Fact p.Prime]
    {alloc : Allocation es} {a b : MainState er es}
    (h : SubexpMainCoefficients.Result alloc a b p r Q R)
    (i : Fin 32) (hi : i ≠ 9) : b.stacks (master alloc i) = a.stacks (master alloc i) := by
  apply h.frame
  · simp only [SubexpLayoutPorts.master_val]
    omega
  · intro he
    exact hi (SubexpLayoutPorts.master_injective alloc he)
  · intro he
    have hv := congrArg Fin.val he
    change 640 + i.val = 254 at hv
    omega

private theorem coefficient_workspace {er es p r Q R : ℕ} [Fact p.Prime]
    {alloc : Allocation es} {a b : MainState er es}
    (h : SubexpMainCoefficients.Result alloc a b p r Q R) (ha : Workspace alloc a) :
    Workspace alloc b := by
  intro i hi
  by_cases hs : i.val < 64
  · exact h.scratch ⟨i.val, hs⟩
  · apply (h.frame _ (by change 64 ≤ i.val; omega) ?_ ?_).trans (ha i hi)
    · intro he
      have hv := congrArg Fin.val he
      change i.val = 649 at hv
      omega
    · intro he
      exact hi (congrArg Fin.val he)

private theorem scalar_master {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (i : Fin 32)
    (hi : i.val < 21 ∨ 27 < i.val) :
    (SubexpMainScalarAlphabet.installed alloc a p).stacks (master alloc i) =
      a.stacks (master alloc i) := by
  apply SubexpMainScalarAlphabet.installed_frame
  · intro j he
    have hv := congrArg Fin.val he
    change 640 + (21 + j.val) = 640 + i.val at hv
    omega
  · intro j he
    have hv := congrArg Fin.val he
    change j.val = 640 + i.val at hv
    omega

private theorem scalar_persistent {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (i : Fin 32) :
    (SubexpMainScalarAlphabet.installed alloc a p).stacks (persistent es i) =
      a.stacks (persistent es i) := by
  apply SubexpMainScalarAlphabet.installed_frame
  · intro j
    exact SubexpLayoutPorts.master_ne_persistent alloc _ i
  · intro j he
    have hv := congrArg Fin.val he
    have hw := alloc.enough.trans alloc.within
    change j.val = workStacks es + i.val at hv
    omega

private theorem scalar_workspace {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (ha : Workspace alloc a) :
    Workspace alloc (SubexpMainScalarAlphabet.installed alloc a p) := by
  intro i hi
  by_cases hs : i.val < 6
  · exact SubexpMainScalarAlphabet.installed_work alloc a p ⟨i.val, hs⟩
  · apply (SubexpMainScalarAlphabet.installed_frame alloc a p _ ?_ ?_).trans (ha i hi)
    · intro j he
      have hv := congrArg Fin.val he
      change 640 + (21 + j.val) = i.val at hv
      omega
    · intro j he
      have hv := congrArg Fin.val he
      change j.val = i.val at hv
      omega

private theorem width_master {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (i : Fin 32) (hi : i ≠ 20) :
    (SubexpMainScalarFrameWidth.installed alloc a).stacks (master alloc i) =
      a.stacks (master alloc i) := by
  apply SubexpMainScalarFrameWidth.installed_frame
  · intro he
    exact hi (SubexpLayoutPorts.master_injective alloc he).symm
  · intro he
    have hv := congrArg Fin.val he
    change 319 = 640 + i.val at hv
    omega

private theorem width_persistent {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (i : Fin 32) :
    (SubexpMainScalarFrameWidth.installed alloc a).stacks (persistent es i) =
      a.stacks (persistent es i) := by
  apply SubexpMainScalarFrameWidth.installed_frame
  · exact SubexpLayoutPorts.master_ne_persistent alloc 20 i
  · intro he
    have hv := congrArg Fin.val he
    have hw := alloc.enough.trans alloc.within
    change 319 = workStacks es + i.val at hv
    omega

private theorem width_workspace {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (ha : Workspace alloc a) :
    Workspace alloc (SubexpMainScalarFrameWidth.installed alloc a) := by
  intro i hi
  by_cases hs : i.val = 319
  · have he : i.castAdd 32 = (319 : Fin 672) := Fin.ext hs
    rw [he]
    exact SubexpMainScalarFrameWidth.installed_work alloc a
  · apply (SubexpMainScalarFrameWidth.installed_frame alloc a _ ?_ ?_).trans (ha i hi)
    · intro he
      have hv := congrArg Fin.val he
      change 660 = i.val at hv
      omega
    · intro he
      exact hs (congrArg Fin.val he).symm

private theorem packing_workspace {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {U : Type*} [DecidableEq U] {s : PackingExecution.Spec U}
    (h : SubexpMainPacking.Result alloc a b s) (ha : Workspace alloc a) : Workspace alloc b := by
  intro i hi
  by_cases hs : i.val < 49
  · exact h.scratch ⟨i.val, hs⟩
  · exact (h.work_frame _ (by change 49 ≤ i.val; omega) i.isLt).trans (ha i hi)

private theorem local_ready {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (ha : Workspace alloc a) :
    SubexpMainLocalBasis.WorkspaceReady alloc hr a := by
  have addresses : ∀ i : Fin 131, i ∉ SubexpLocalBasisReady.occupied →
      (SubexpMainLocalBasisPorts.address i).val < 640 ∧
      (SubexpMainLocalBasisPorts.address i).val ≠ 254 := by decide
  intro i hi
  obtain ⟨hlo, hne⟩ := addresses i hi
  change a.stacks (SubexpMainLocalBasisPorts.location alloc
    (SubexpMainLocalBasisPorts.address i)) = []
  rw [SubexpMainLocalBasisPorts.location, dite_eq_left (by omega)]
  exact ha ⟨_, hlo⟩ hne

private theorem local_master {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (ha : Workspace alloc a)
    (i : Fin 32) (hi : i ≠ 14) :
    (SubexpMainLocalBasis.result alloc hr a output).stacks (master alloc i) =
      a.stacks (master alloc i) := by
  apply SubexpMainLocalBasisFrame.result_preserved alloc hr a output (local_ready alloc hr a ha)
  · intro he
    have hv := congrArg Fin.val he
    change 640 + i.val = 111 at hv
    omega
  · intro he
    exact hi (SubexpLayoutPorts.master_injective alloc he)

private theorem local_persistent {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (ha : Workspace alloc a) (i : Fin 32) :
    (SubexpMainLocalBasis.result alloc hr a output).stacks (persistent es i) =
      a.stacks (persistent es i) := by
  apply SubexpMainLocalBasisFrame.result_preserved alloc hr a output (local_ready alloc hr a ha)
  · intro he
    have hv := congrArg Fin.val he
    have hw := alloc.enough.trans alloc.within
    change workStacks es + i.val = 111 at hv
    omega
  · exact (SubexpLayoutPorts.master_ne_persistent alloc 14 i).symm

private theorem local_workspace {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (ha : Workspace alloc a) :
    Workspace alloc (SubexpMainLocalBasis.result alloc hr a output) := by
  intro i hi
  rw [SubexpMainLocalBasis.result_stacks alloc hr a output (local_ready alloc hr a ha)]
  have hm : ordinary alloc (i.castAdd 32) ≠ master alloc 14 := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 654 at hv
    omega
  rw [Function.update_of_ne hm]
  by_cases hs : ordinary alloc (i.castAdd 32) = ordinary alloc 111
  · rw [hs, Function.update_self]
  · rw [Function.update_of_ne hs]
    exact ha i hi

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p r Q Δ R D : ℕ) [Fact p.Prime] [NeZero r] (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (tables : List (List Bool)) where
  first : MulticolorTypes.Word r Q
  tail : List (MulticolorTypes.Word r Q)
  nodup : (first :: tail).Nodup
  complete : ∀ w, w ∈ first :: tail
  prefixResult : SubexpMainLayoutPrefix.Result alloc a b r Q Δ D scopes hd first tail tables
  coefficients : Fin R → ZMod p
  coefficientBytes : b.stacks (master alloc 9) = CoefficientSearchSemantics.encode p coefficients
  coefficientCorrect : CoefficientNormalization.unnormalize (List.ofFn coefficients) =
    CoefficientSearch.coefficientsNat p (TailInterval.intervalStart r Q R) R
  wordWidth : List Bool
  wordWidth_length : wordWidth.length = Q * r
  widthBytes : b.stacks (master alloc 4) = wordWidth
  packingOutputs : ∀ i, b.stacks (master alloc (SubexpMainPacking.outputIndex i)) =
    SubexpMainPacking.outputBytes
      (PackingCanonicalSpec.specWithWidth hr hQ scopes hd first tail wordWidth wordWidth_length) i
  scalar : ∀ i, b.stacks (SubexpMainScalarAlphabet.targetPort alloc i) =
    SubexpMainScalarAlphabet.targetWord p i
  scalarWidth : b.stacks (master alloc 20) = List.replicate (GlobalBasisEntry.frameWidth p) true
  rows : List (List (List Bool))
  rowsGood : LocalBasisBatchProgram.RowsGood
    (LocalBasisBatchProgram.GoodResult (Δ := Δ) p hr hQ (List.ofFn coefficients)) r Q rows
  basisBytes : b.stacks (master alloc 14) =
    ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)
  workspace : Workspace alloc b

noncomputable abbrev Result.packing {er es p r Q Δ R D : ℕ} [Fact p.Prime] [NeZero r]
    {alloc : Allocation es} {a b : MainState er es} {hr : 0 < r} {hQ : 0 < Q}
    {scopes : List (List ℕ)} {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {tables : List (List Bool)} (h : Result alloc a b p r Q Δ R D hr hQ scopes hd tables) :=
  PackingCanonicalSpec.specWithWidth hr hQ scopes hd h.first h.tail h.wordWidth h.wordWidth_length

def afterPrefix (er : ℕ) (hregs : 16 ≤ er) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpMainCoefficients.procedure er alloc)
    (SubexpProcedureCompose.sequence (SubexpMainScalarAlphabet.procedure er alloc)
      (SubexpProcedureCompose.sequence (SubexpMainScalarFrameWidth.procedure er alloc)
        (SubexpProcedureCompose.sequence (SubexpMainPacking.procedure er alloc)
          (SubexpMainLocalBasis.procedure er hregs alloc))))

def selectedSize {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  stackBits ((SubexpMainCoefficients.procedure er alloc).project a).stacks

private theorem wordBound_stackBits {r s : ℕ} (a : State r s) :
    SubexpSetupStorage.WordBound (stackBits a.stacks) a := by
  intro i
  exact Finset.single_le_sum (fun (j : Fin s) _ => Nat.zero_le (a.stacks j).length)
    (Finset.mem_univ i)

noncomputable def tailBound {er es p r Q Δ R D : ℕ} [Fact p.Prime] [NeZero r]
    (alloc : Allocation es) (hregs : 16 ≤ er) (a start coefficientState packingState out : MainState er es)
    {hr : 0 < r} {hQ : 0 < Q} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ} {tables : List (List Bool)}
    (result : Result alloc a out p r Q Δ R D hr hQ scopes hd tables) : ℕ :=
  SubexpCoefficientProgram.budget p r Q R (selectedSize alloc start) +
    SubexpMainScalarAlphabet.runtimeBound alloc coefficientState p +
    SubexpMainScalarFrameWidth.runtimeBound alloc
      (SubexpMainScalarAlphabet.installed alloc coefficientState p) +
    SubexpMainPacking.runtimeBound alloc
      (SubexpMainScalarFrameWidth.installed alloc
        (SubexpMainScalarAlphabet.installed alloc coefficientState p)) result.packing +
    SubexpMainLocalBasis.executionBound (Δ := Δ) alloc hregs packingState p hr hQ
      (List.ofFn result.coefficients) (CoefficientSearchSemantics.alphabet p) + 4

private theorem after_prefix_execution {er es p r Q Δ R D : ℕ} [Fact p.Prime] [NeZero r]
    (alloc : Allocation es) (hregs : 16 ≤ er) (a start : MainState er es)
    (hr : 0 < r) (hQ : 0 < Q) (h2 : (2 : ZMod p) ≠ 0)
    (scopes : List (List ℕ)) (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (tables : List (List Bool)) (first : MulticolorTypes.Word r Q)
    (tail : List (MulticolorTypes.Word r Q)) (hnodup : (first :: tail).Nodup)
    (hcomplete : ∀ w, w ∈ first :: tail)
    (hpref : SubexpMainLayoutPrefix.Result alloc a start r Q Δ D scopes hd first tail tables)
    (hstart14 : start.stacks (master alloc 14) = a.stacks (master alloc 14))
    (hw : SubexpMainLayoutPrefixWorkspace.WorkspaceEmpty alloc start)
    (hpw : CounterPrograms.value (a.stacks (persistent es 6)) = p)
    (hrw : CounterPrograms.value (a.stacks (persistent es 21)) = r)
    (hQw : CounterPrograms.value (a.stacks (persistent es 17)) = Q)
    (hRw : CounterPrograms.value (a.stacks (persistent es 25)) = R) :
    ∃ coefficientState packingState out n,
      ∃ result : Result alloc a out p r Q Δ R D hr hQ scopes hd tables,
        n ≤ tailBound alloc hregs a start coefficientState packingState out result ∧
        EntryFacts alloc a packingState ∧
        Eval (afterPrefix er hregs alloc).invoke n start out := by
  have hselected : SubexpSetupStorage.WordBound (selectedSize alloc start)
      ((SubexpMainCoefficients.procedure er alloc).project start) :=
    wordBound_stackBits ((SubexpMainCoefficients.procedure er alloc).project start)
  obtain ⟨nc, e, hec, hnc, ⟨hc⟩⟩ := SubexpMainCoefficients.invoke_run_selected alloc p r Q R
    (selectedSize alloc start) hr h2 start hselected
    (fun i => hw ⟨i.val, by omega⟩)
    (by rw [hpref.persistent]; exact hpw) (by rw [hpref.persistent]; exact hrw)
    (by rw [hpref.persistent]; exact hQw) (by rw [hpref.persistent]; exact hRw)
  have heprefix := prefix_transport hpref
    (fun i hi => coefficient_master hc i (by
      have h : ∀ j : Fin 32, (j.val ≤ 8 ∨ j = 10) → j ≠ 9 := by decide
      exact h i hi)) hc.persistent_frame hc.control
  have hework := coefficient_workspace hc (fun i _ => hw i)
  let f := SubexpMainScalarAlphabet.installed alloc e p
  obtain ⟨ns, hns, hes⟩ := SubexpMainScalarAlphabet.execution alloc e p
    (by rw [heprefix.persistent]; exact hpw)
  have hfprefix := prefix_transport heprefix
    (fun i hi => scalar_master alloc e p i (by
      have h : ∀ j : Fin 32, (j.val ≤ 8 ∨ j = 10) → j.val < 21 ∨ 27 < j.val := by decide
      exact h i hi)) (scalar_persistent alloc e p) (SubexpMainScalarAlphabet.installed_control alloc e p)
  have hfwork := scalar_workspace alloc e p hework
  let g := SubexpMainScalarFrameWidth.installed alloc f
  have hew := SubexpMainScalarFrameWidth.execution alloc f
  have hgprefix := prefix_transport hfprefix
    (fun i hi => width_master alloc f i (by
      have h : ∀ j : Fin 32, (j.val ≤ 8 ∨ j = 10) → j ≠ 20 := by decide
      exact h i hi)) (width_persistent alloc f) (SubexpMainScalarFrameWidth.installed_control alloc f)
  have hgwork := width_workspace alloc f hfwork
  let width := g.stacks (master alloc 4)
  have hwidth : width.length = Q * r := hgprefix.width
  let spec := PackingCanonicalSpec.specWithWidth hr hQ scopes hd first tail width hwidth
  have hinput : SubexpMainPacking.inputs alloc g = spec.params.input := by
    change SubexpMainPacking.inputs alloc g = (PackingCanonicalSpec.params scopes hd first tail width).input
    rw [SubexpMainPacking.inputs_eq, PackingCanonicalSpec.input_eq]
    have hrows : g.stacks (master alloc 2) = (PackingCanonicalSpec.rows scopes hd first tail).flatten :=
      hgprefix.assignment
    rw [hrows, hgprefix.scopeBytes, hgprefix.alphabet]
    rw [show g.stacks (master alloc 8) = List.replicate D true from hgprefix.headers 3,
      show g.stacks (master alloc 7) = List.replicate Δ true from hgprefix.headers 2]
  obtain ⟨np, hnp, h, hep, hp⟩ := SubexpMainPacking.execution alloc g spec hinput
  have hhprefix := prefix_transport hgprefix
    (fun i hi => hp.master_frame i (by
      have hf : ∀ j : Fin 32, (j.val ≤ 8 ∨ j = 10) → j ∉ SubexpMainPacking.writtenMasters := by decide
      exact hf i hi)) hp.persistent_frame hp.controls
  have hhwork := packing_workspace hp hgwork
  have hentry : EntryFacts alloc a h := {
    workspace := hhwork
    persistent := hhprefix.persistent
    oldBasisOutput := (hp.master_frame 14 (by decide)).trans
      ((width_master alloc f 14 (by decide)).trans
        ((scalar_master alloc e p 14 (by decide)).trans
          ((coefficient_master hc 14 (by decide)).trans hstart14))) }
  have hhcoeff : h.stacks (master alloc 9) = CoefficientSearchSemantics.encode p hc.coefficients :=
    (hp.master_frame 9 (by decide)).trans ((width_master alloc f 9 (by decide)).trans
      ((scalar_master alloc e p 9 (by decide)).trans hc.output))
  have hhscalar (i : Fin 7) : h.stacks (SubexpMainScalarAlphabet.targetPort alloc i) =
      SubexpMainScalarAlphabet.targetWord p i := by
    let j : Fin 32 := scalarIndex i
    have hnot : j ∉ SubexpMainPacking.writtenMasters := by
      have hf : ∀ k : Fin 7, scalarIndex k ∉ SubexpMainPacking.writtenMasters := by decide
      exact hf i
    exact (hp.master_frame j hnot).trans ((width_master alloc f j (by
      intro he; have hv := congrArg Fin.val he; dsimp [j, scalarIndex] at hv; omega)).trans
        (SubexpMainScalarAlphabet.installed_target alloc e p i))
  have hhwidth : h.stacks (master alloc 20) = List.replicate (GlobalBasisEntry.frameWidth p) true :=
    (hp.master_frame 20 (by decide)).trans (SubexpMainScalarFrameWidth.after_scalar_alphabet alloc e p)
  have hlocal : SubexpMainLocalBasis.CanonicalInputs alloc hregs h p r Q Δ
      (List.ofFn hc.coefficients) (CoefficientSearchSemantics.alphabet p) := by
    constructor
    · exact hhprefix.universal
    · exact hhscalar 2
    · exact hhscalar 0
    · exact hhcoeff.trans (CoefficientSearchProgram.encode_eq_valueWords p hc.coefficients)
    · rw [hhprefix.persistent, hRw, List.length_ofFn]
    · exact hhprefix.headers 0
    · exact hhprefix.headers 1
    · exact hhprefix.headers 2
    · have ht := hhscalar 3
      change h.stacks (master alloc 24) = ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p) at ht
      rw [ScalarSetupProgram.tokenAlphabet_eq] at ht
      exact ht
  obtain ⟨rows, hgood, nl, hnl, hel⟩ := SubexpMainLocalBasis.execution alloc hregs h p h2 hr hQ
    (List.ofFn hc.coefficients) (CoefficientSearchSemantics.alphabet p)
    (CoefficientSearchSemantics.alphabet_complete p) (local_ready alloc hregs h hhwork) hlocal
  let bytes := ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)
  let out := SubexpMainLocalBasis.result alloc hregs h bytes
  have houtprefix := prefix_transport hhprefix
    (fun i hi => local_master alloc hregs h bytes hhwork i (by
      have hf : ∀ j : Fin 32, (j.val ≤ 8 ∨ j = 10) → j ≠ 14 := by decide
      exact hf i hi)) (local_persistent alloc hregs h bytes hhwork)
      (SubexpMainLocalBasisFrame.result_control alloc hregs h bytes)
  let result : Result alloc a out p r Q Δ R D hr hQ scopes hd tables := {
    first := first, tail := tail, nodup := hnodup, complete := hcomplete, prefixResult := houtprefix
    coefficients := hc.coefficients
    coefficientBytes := (local_master alloc hregs h bytes hhwork 9 (by decide)).trans hhcoeff
    coefficientCorrect := hc.correct
    wordWidth := width, wordWidth_length := hwidth
    widthBytes := (local_master alloc hregs h bytes hhwork 4 (by decide)).trans (hp.inputs 1)
    packingOutputs := fun i => (local_master alloc hregs h bytes hhwork
      (SubexpMainPacking.outputIndex i) (by
        have hf : ∀ j : Fin 6, SubexpMainPacking.outputIndex j ≠ 14 := by decide
        exact hf i)).trans (hp.outputs i)
    scalar := fun i => (local_master alloc hregs h bytes hhwork ⟨21 + i.val, by omega⟩
      (by intro he; have hv := congrArg Fin.val he; dsimp at hv; omega)).trans (hhscalar i)
    scalarWidth := (local_master alloc hregs h bytes hhwork 20 (by decide)).trans hhwidth
    rows := rows, rowsGood := hgood
    basisBytes := SubexpMainLocalBasisFrame.result_output alloc hregs h bytes (local_ready alloc hregs h hhwork)
    workspace := local_workspace alloc hregs h bytes hhwork }
  have hrun := SubexpProcedureCompose.sequence_invoke _ _ hec
    (SubexpProcedureCompose.sequence_invoke _ _ hes
      (SubexpProcedureCompose.sequence_invoke _ _ hew
        (SubexpProcedureCompose.sequence_invoke _ _ hep hel)))
  refine ⟨e, h, out, _, result, ?_, hentry, hrun⟩
  change _ ≤ SubexpCoefficientProgram.budget p r Q R (selectedSize alloc start) +
    SubexpMainScalarAlphabet.runtimeBound alloc e p +
    SubexpMainScalarFrameWidth.runtimeBound alloc f + SubexpMainPacking.runtimeBound alloc g spec +
    SubexpMainLocalBasis.executionBound (Δ := Δ) alloc hregs h p hr hQ
      (List.ofFn hc.coefficients) (CoefficientSearchSemantics.alphabet p) + 4
  omega

/-- Execute the literal fixed choices program from the typed leaf and its
numeric width/occurrence bounds. The intermediate states in the bound are
the actual successive outputs of the invoked programs. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p r Q Δ R k B : ℕ) [Fact p.Prime] [NeZero r]
    (hr : 0 < r) (hQ : 0 < Q) (h2 : (2 : ZMod p) ≠ 0)
    (hell : 0 < CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell)
    (hwidth : CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤
      (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus.length)
    (hp : 0 < BinaryArithmetic.toNat (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus)
    (G : SubexpLeafData.Leaf
      (SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a)))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hsource : (SubexpMainLayout.Factors.sourceInputs alloc a).leaf =
      Encoding.encodeList SubexpClauseRowProgram.clauseBytes G)
    (hD : SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) =
      ChunkPartition.count
        (SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a))
        (CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell))
    (hcap : 2 ^ CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤ p)
    (hk : 1 ≤ k) (hw : SAT.WidthAtMost k (ExecCNF.formulaSet G))
    (ho : SAT.OccurrenceAtMost B (ExecCNF.formulaSet G)) (hne : [] ∉ G)
    (hdelta : 1 + CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell * B ≤ Δ)
    (hmeta : ∀ i, CounterPrograms.value
      (a.stacks (persistent es (SubexpMainAssignment.metadataIndex i))) =
      (![r, Q, Δ, SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)] :
        Fin 4 → ℕ) i)
    (hzero : ∀ i : Fin 672, a.stacks (ordinary alloc i) = [])
    (hpw : CounterPrograms.value (a.stacks (persistent es 6)) = p)
    (hrw : CounterPrograms.value (a.stacks (persistent es 21)) = r)
    (hQw : CounterPrograms.value (a.stacks (persistent es 17)) = Q)
    (hRw : CounterPrograms.value (a.stacks (persistent es 25)) = R) :
    let hv := SubexpLayoutConstruction.family_valid
      (SubexpMainLayout.Factors.sourceInputs alloc a) hp hell hwidth hD
    let scopes := SubexpLayoutScopeOrder.orderedScopes
      (SubexpMainLayout.Factors.sourceInputs alloc a) G hG hell
    ∃ hd : ∀ v : Fin (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)),
        IncidencePlanSpec.degree scopes v.val ≤ Δ,
      ∃ factorState assignmentState start coefficientState packingState out n,
        ∃ result : Result alloc a out p r Q Δ R
          (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
          hr hQ scopes hd
          (SubexpLayoutConstruction.tables (SubexpMainLayout.Factors.sourceInputs alloc a) hv G),
          n ≤ SubexpMainLayoutPrefix.runtimeBound alloc a factorState assignmentState hv G hG hell r Q Δ +
            tailBound alloc hregs a start coefficientState packingState out result + 1 ∧
          EntryFacts alloc a packingState ∧
          Eval (SubexpMainLayoutProgram.choices er hregs alloc).invoke n a out := by
  dsimp only
  let I := SubexpMainLayout.Factors.sourceInputs alloc a
  let hv := SubexpLayoutConstruction.family_valid I hp hell hwidth hD
  let scopes := SubexpLayoutScopeOrder.orderedScopes I G hG hell
  let D := SubexpLayoutConstruction.dimension I
  have hd (v : Fin D) : IncidencePlanSpec.degree scopes v.val ≤ Δ :=
    (SubexpLayoutScopeOrder.degree_le I G hG hell hD hcap hk hw ho hne v).trans hdelta
  obtain ⟨nf, hnf, factorState, hef, hf⟩ :=
    SubexpMainLayout.Factors.execution alloc a hell hwidth hv G hsource
  have hs : factorState.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes :=
    hf.scopes.trans (SubexpLayoutScopeOrder.scope_stream_eq I hv G hG hell hD)
  have hm (i : Fin 4) : CounterPrograms.value
      (factorState.stacks (persistent es (SubexpMainAssignment.metadataIndex i))) =
      (![r, Q, Δ, D] : Fin 4 → ℕ) i := by
    rw [SubexpMainLayoutPrefix.factors_persistent_frame hf]
    exact hmeta i
  obtain ⟨first, tail, na, hna, assignmentState, hnodup, hcomplete, hea, ha⟩ :=
    SubexpMainAssignment.execution alloc factorState r Q Δ D scopes hd hm hs
  obtain ⟨nu, hnu, start, heu, hu⟩ := SubexpMainUniversalTypes.execution alloc assignmentState
    r Q Δ ha.alphabet (ha.headers 2)
  have hpref := SubexpMainLayoutPrefix.result_of_stages hf hs ha hu
  have hz := SubexpMainLayoutPrefixWorkspace.workspace_of_stages hf ha hu
    (fun i => hzero (i.castAdd 32))
  have hstart14 : start.stacks (master alloc 14) = a.stacks (master alloc 14) :=
    (hu.master_frame 14 (by decide)).trans
      ((ha.master_frame 14 (by decide)).trans (factors_master14 hf))
  have hpre := SubexpProcedureCompose.sequence_invoke _ _ hef
    (SubexpProcedureCompose.sequence_invoke _ _ hea heu)
  have hnp : nf + (na + nu + 1) + 1 ≤
      SubexpMainLayoutPrefix.runtimeBound alloc a factorState assignmentState hv G hG hell r Q Δ := by
    change nf + (na + nu + 1) + 1 ≤ SubexpMainLayout.Factors.runtimeBound alloc a hv G +
      SubexpMainAssignment.runtimeBound alloc factorState r Q Δ D scopes +
      SubexpMainUniversalTypes.runtimeBound alloc assignmentState r Q Δ + 2
    omega
  obtain ⟨coefficientState, packingState, out, nt, result, hnt, hentry, ht⟩ :=
    after_prefix_execution alloc hregs a start hr hQ h2 scopes hd _ first tail
      hnodup hcomplete hpref hstart14 hz hpw hrw hQw hRw
  refine ⟨hd, factorState, assignmentState, start, coefficientState, packingState,
    out, (nf + (na + nu + 1) + 1) + nt + 1, result, by omega, hentry, ?_⟩
  exact SubexpProcedureCompose.sequence_invoke _ _ hpre ht

end SubexponentialSAT.SubexpMainLayoutChoices

end OAI.Algorithms
