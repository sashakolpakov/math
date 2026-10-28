import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowsBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutRowsTrace

namespace OAI.Algorithms

/-! A fixed polynomial for the complete row phase, including actual
preparation and clearing, from word bounds propagated along real traces. -/

namespace SubexponentialSAT.SubexpMainLayoutRowBounds

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpMainLayoutWordBounds (RelevantWordBound)
open SubexpLiftRing SubexpQuarticRing SubexpDenseRowTableProgram
open Subexp.ConstructivePacking

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem sum_map_le {α : Type*} (l : List α) (f : α → ℕ) (W : ℕ)
    (h : ∀ x ∈ l, f x ≤ W) : (l.map f).sum ≤ l.length * W := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

private theorem preclear_word_le {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (j : Fin (totalStacks es)) :
    ((SubexpMainRowPreparation.pre alloc a).stacks j).length ≤ (a.stacks j).length := by
  change ((SubexpMainRowPreclear.result alloc a).stacks j).length ≤ _
  rw [SubexpMainRowPreclear.result_stack]
  split_ifs <;> simp

theorem preclear_bound {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (W : ℕ) (hW : RelevantWordBound W a) :
    SubexpMainRowPreclear.runtimeBound alloc a ≤ 158 * W + 238 := by
  have hs := sum_map_le SubexpMainRowPreclear.ports
    (fun i => (a.stacks (SubexpMainRowPreclear.stackMap alloc i)).length) W (by
      intro i hi
      apply hW
      exact Or.inl (by change i.val < 672; have := i.isLt; omega))
  rw [SubexpMainRowPreclear.ports_length] at hs
  rw [SubexpMainRowPreclear.runtimeBound_eq]
  change 2 * (SubexpMainRowPreclear.ports.map
    (fun i => (a.stacks (SubexpMainRowPreclear.stackMap alloc i)).length)).sum + 238 ≤ _
  omega

theorem context_words {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (W : ℕ) (hW : RelevantWordBound W a) :
    ∀ i, ((SubexpMainRowContext.input alloc a).stacks i).length ≤ W := by
  intro i
  change ((SubexpMainRowPreparation.pre alloc a).stacks
    (SubexpSourceRowContext.Main.stackMap (SubexpMainRowSetup.contextAllocation alloc) i)).length ≤ W
  apply (preclear_word_le alloc a _).trans
  by_cases hr : i = SubexpSourceRowContext.radiusInput
  · subst i
    simp only [SubexpSourceRowContext.Main.stackMap]
    exact hW _ (Or.inr ⟨25, rfl, Or.inl (by norm_num [SubexpMainInvariant.ParameterPort])⟩)
  by_cases ht : i = SubexpSourceRowContext.targetWidthInput
  · subst i
    simp only [SubexpSourceRowContext.Main.stackMap, ite_eq_right hr]
    exact hW _ (Or.inr ⟨13, rfl, Or.inr (Or.inl (by norm_num [SubexpMainInvariant.CachePort]))⟩)
  simp only [SubexpSourceRowContext.Main.stackMap, ite_eq_right hr, ite_eq_right ht]
  apply hW
  exact Or.inl (by change i.val < 672; have := i.isLt; omega)

theorem header_bound {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (W : ℕ) (hW : RelevantWordBound W a) :
    SubexpMainRowHeader.runtimeBound alloc (SubexpMainRowPreparation.pre alloc a) ≤
      100 * (13 * W + 1) + 1 := by
  have hw (i : Fin 13) :
      (((SubexpMainRowHeader.procedure er alloc).project
        (SubexpMainRowPreparation.pre alloc a)).stacks i).length ≤ W := by
    change ((SubexpMainRowPreparation.pre alloc a).stacks
      (SubexpMainRowHeader.stackMap alloc i)).length ≤ W
    apply (preclear_word_le alloc a _).trans
    apply hW
    apply Or.inl
    fin_cases i <;> norm_num [SubexpMainRowHeader.stackMap, master, ordinary]
  have hs' : BitProgram.stackBits (((SubexpMainRowHeader.procedure er alloc).project
      (SubexpMainRowPreparation.pre alloc a)).stacks) ≤ 13 * W := by
    unfold BitProgram.stackBits
    calc
      _ ≤ ∑ _ : Fin 13, W := Finset.sum_le_sum fun i _ => hw i
      _ = 13 * W := by simp
  unfold SubexpMainRowHeader.runtimeBound
  omega

theorem preparation_bound {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (W R : ℕ) (hW : RelevantWordBound W a)
    (hR : CounterPrograms.value (a.stacks (persistent es 25)) = R) :
    SubexpMainRowPreparation.runtimeBound alloc a ≤ 10000 * (W + R + 1)^2 := by
  have hc := preclear_bound alloc a W hW
  have hh := header_bound alloc a W hW
  have hctx := SubexpSourceRowContext.runtimeBound_le (SubexpMainRowContext.input alloc a) (W + R)
    (fun i => (context_words alloc a W hW i).trans (by omega)) (by
      rw [SubexpMainRowContext.input_radius, ← CounterPrograms.value_eq_toNat, hR]
      omega)
  change SubexpMainRowPreclear.runtimeBound alloc a +
    (SubexpSourceRowContext.runtimeBound (SubexpMainRowContext.input alloc a) +
      SubexpMainRowHeader.runtimeBound alloc (SubexpMainRowPreparation.pre alloc a) + 1) + 1 ≤ _
  nlinarith [Nat.zero_le (W^2), Nat.zero_le (R^2), Nat.zero_le (W * R)]

/-- All quantities are runtime parameters or lengths of selected words. -/
def scale (p r Q Δ D μ R N W : ℕ) : ℕ :=
  W + r + Q + Δ + D + R + baseWidth p 1 + baseWidth p μ +
    Subexp.CollisionProgram.typeWidth r Q Δ + N + 1

def nativeEnvelope (S : ℕ) : ℕ :=
  let K := Subexp.UniversalRowAssemblyBound.uniformBound (16 * S) + 1
  tablePolynomialBound S S
    (SubexpDenseRowServiceBound.serviceBound S S S S S S S S K K)
    ((S + 1) * (4 * S)) S

def polynomial (S : ℕ) : ℕ := 10^40 * S^13

theorem envelope_le (S : ℕ) (hS : 1 ≤ S) :
    10000 * S^2 + nativeEnvelope S + 1 ≤ polynomial S := by
  have hp (n : ℕ) (hn : n ≤ 13) : S^n ≤ S^13 := Nat.pow_le_pow_right hS hn
  have h0 : 1 ≤ S^13 := by simpa using hp 0 (by decide)
  have h1 : S ≤ S^13 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  have h9 := hp 9 (by decide)
  have h10 := hp 10 (by decide)
  have h11 := hp 11 (by decide)
  have h12 := hp 12 (by decide)
  unfold nativeEnvelope polynomial tablePolynomialBound
    SubexpDenseRowServiceBound.serviceBound SubexpDenseRowServiceBound.dispatchBound
    SubexpRowToTaylor.runtimeBound SubexpRowCost.scale Subexp.UniversalRowAssemblyBound.uniformBound
  ring_nf
  omega

theorem inputSourceSize_le {er es : ℕ} (p r Q Δ D μ R N W : ℕ)
    (alloc : Allocation es) (a : MainState er es) (hW : RelevantWordBound W a) :
    SubexpMainRowsBounds.inputSourceSize p r Q Δ R alloc a ≤ 16 * scale p r Q Δ D μ R N W := by
  have ho (i : Fin 672) : (a.stacks (ordinary alloc i)).length ≤ W := hW _ (Or.inl i.isLt)
  have hm (i : Fin 32) : (a.stacks (master alloc i)).length ≤ W := ho ⟨640 + i.val, by omega⟩
  have h128 := ho 128
  have h129 := ho 129
  have h131 := ho 131
  have h132 := ho 132
  have h133 := ho 133
  have h134 := ho 134
  have h135 := ho 135
  have h136 := ho 136
  have h137 := ho 137
  have h5 := hm 5
  have h6 := hm 6
  have h9 := hm 9
  unfold SubexpMainRowsBounds.inputSourceSize scale Subexp.MatrixWordEncoding.width
  simp only [List.sum_cons, List.sum_nil]
  omega

theorem inputRuntimeBound_le {er es : ℕ} (p r Q Δ D μ R W : ℕ)
    (scopes : List (List ℕ)) (alloc : Allocation es) (a : MainState er es)
    (hW : RelevantWordBound W a) :
    SubexpMainRowsBounds.inputRuntimeBound p r Q Δ D μ R scopes alloc a ≤
      nativeEnvelope (scale p r Q Δ D μ R (scopesCode scopes).length W) := by
  let S := scale p r Q Δ D μ R (scopesCode scopes).length W
  have hparams : R ≤ S ∧ D ≤ S ∧ baseWidth p 1 ≤ S ∧ baseWidth p μ ≤ S ∧
      Subexp.CollisionProgram.typeWidth r Q Δ ≤ S ∧ (scopesCode scopes).length ≤ S ∧ W ≤ S := by
    dsimp [S, scale]
    omega
  rcases hparams with ⟨hR, hD, hb, hB, ht, hN, hWS⟩
  have hE : scopes.length ≤ S := by
    have hn := Encoding.length_encodeList_lower scopeCode scopes
    change scopes.length + 1 ≤ (scopesCode scopes).length at hn
    omega
  have hscope : (SubexpIncidenceSlotProgram.scopeBits scopes).length ≤ S := hN
  have hL : (a.stacks (master alloc 13)).length ≤ S :=
    (hW _ (Or.inl (by change 653 < 672; decide))).trans hWS
  have hs := inputSourceSize_le p r Q Δ D μ R (scopesCode scopes).length W alloc a hW
  have hk := Subexp.UniversalRowAssemblyBound.monotone_uniformBound hs
  have hk' := Nat.add_le_add_right hk 1
  change SubexpMainRowsBounds.inputRuntimeBound p r Q Δ D μ R scopes alloc a ≤ nativeEnvelope S
  unfold SubexpMainRowsBounds.inputRuntimeBound nativeEnvelope tablePolynomialBound
    SubexpDenseRowServiceBound.serviceBound SubexpDenseRowServiceBound.dispatchBound
    SubexpDenseRowServiceBound.rowLength SubexpRowToTaylor.runtimeBound SubexpRowCost.scale
  dsimp only
  gcongr

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (xs : List (ZMod p)) (inverse negative : Fin Q → Word)
  (difference : Fin Q → Fin Q → Word)
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
variable (scopes : List (List ℕ))
variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

/-- The full measured row phase, including old selected-work clearing,
has a fixed polynomial bound from actual input word lengths. -/
theorem runtimeBound_le {er es : ℕ} (hr : 16 ≤ er) (alloc : Allocation es)
    (a : MainState er es) (μ W : ℕ)
    (h : SubexpMainRows.Inputs source xs inverse negative difference P scopes alloc a)
    (hW : RelevantWordBound W a) (h2 : (2 : ZMod p) ≠ 0) :
    SubexpMainRows.runtimeBound source xs inverse negative difference P scopes hd hr alloc a μ ≤
      polynomial (scale p r Q Δ D μ xs.length (scopesCode scopes).length W) := by
  let S := scale p r Q Δ D μ xs.length (scopesCode scopes).length W
  have hS : 1 ≤ S := by dsimp [S, scale]; omega
  have hsmall : W + xs.length + 1 ≤ S := by dsimp [S, scale]; omega
  have hp := (preparation_bound alloc a W xs.length hW h.radius).trans
    (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hsmall 2))
  have hn : SubexpMainRowsBounds.inputRuntimeBound p r Q Δ D μ xs.length scopes alloc a ≤
      nativeEnvelope S := inputRuntimeBound_le p r Q Δ D μ xs.length W scopes alloc a hW
  calc
    _ ≤ SubexpMainRowPreparation.runtimeBound alloc a +
        SubexpMainRowsBounds.inputRuntimeBound p r Q Δ D μ xs.length scopes alloc a + 1 :=
      SubexpMainRowsBounds.runtimeBound_le_input source xs inverse negative difference P scopes hd
        hr alloc a μ h h2
    _ ≤ 10000 * S^2 + nativeEnvelope S + 1 := by omega
    _ ≤ polynomial S := envelope_le S hS

end SubexponentialSAT.SubexpMainLayoutRowBounds

namespace SubexponentialSAT.SubexpMainLayoutRowBounds

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation)
open SubexpMainLayoutWordBounds (RelevantWordBound)
open Subexp.ConstructivePacking
open SubexpDenseRowTableProgram

variable {p r Δ D : ℕ} [Fact p.Prime]
variable (xs : List (ZMod p))
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r (p^4 - 1) Δ))
variable (scopes : List (List ℕ))
variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

/-- Apply the bound to the very state produced by the recorded cache and
Lagrange runs. The row inputs come from that same actual trace record. -/
theorem afterLagrange_bound {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es}
    (result : SubexpMainLayoutRows.Result xs P scopes hd hr alloc a out)
    (trace : SubexpMainLayoutRowsTrace.StageTrace xs P scopes hd result)
    (W : ℕ) (hW : RelevantWordBound W result.afterLagrange) (h2 : (2 : ZMod p) ≠ 0) :
    SubexpMainRows.runtimeBound result.cacheFacts.source xs result.cacheFacts.inverse
      result.cacheFacts.negative result.cacheFacts.difference P scopes hd hr alloc result.afterLagrange (D + 1) ≤
      polynomial (scale p r (p^4 - 1) Δ D (D + 1) xs.length (scopesCode scopes).length W) :=
  runtimeBound_le result.cacheFacts.source xs result.cacheFacts.inverse result.cacheFacts.negative
    result.cacheFacts.difference P scopes hd hr alloc result.afterLagrange (D + 1) W trace.rowInputs hW h2

end SubexponentialSAT.SubexpMainLayoutRowBounds

end OAI.Algorithms
