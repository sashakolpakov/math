import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProgramBuilder
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorCode

namespace OAI.Algorithms

/-!
# Computing the factor records consumed by the separated program builder

The source stores finite row expressions rather than Taylor coefficients.
Every incidence is compiled and shifted once, and the resulting arrays are
captured by the generated `FactorData.taylor` function. Preprocessing counters
sum the actual expression-compilation, shift, and coefficient-lookup counters.
-/

namespace SubexponentialSAT.SubexpFactorCode

open scoped BigOperators
open SubexpRowInterpolation (PolynomialCode)
open SubexpTaylorCode

/-- Input data before Taylor preprocessing at a chosen node. -/
structure FactorSource (D p r : ℕ) (K A : Type*) where
  arity : ℕ
  color : Fin r
  origin : Fin arity → Fin D → K
  rows : Fin arity → Fin D → PolynomialCode A
  table : List (SubexpTableInterpolation.Row p arity A)

structure FactorResult (D p q r : ℕ) (K A : Type*) where
  data : SubexpProgramBuilder.FactorData D p q r K A
  compileOps : ℕ
  shiftOps : ℕ
  listReads : ℕ

private def emptyCache (A : Type*) : CompiledTaylorCache A :=
  ⟨⟨#[], 0, 0⟩, 0⟩

/-- Build all incidence caches eagerly before exposing coefficient lookup. -/
def buildFactor {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) : FactorResult D p q r K A :=
  let caches := Array.ofFn (fun i : Fin source.arity => buildCodeTaylor θ q (source.rows i))
  ⟨{ arity := source.arity
     color := source.color
     origin := source.origin
     taylor := fun i => coefficients (D := D) (q := q)
       (caches.getD i.val (emptyCache A)).taylor
     table := source.table },
    (caches.toList.map CompiledTaylorCache.compileOps).sum,
    (caches.toList.map (fun c => c.taylor.scalarOps)).sum,
    (caches.toList.map (fun c => c.taylor.listReads)).sum⟩

@[simp] theorem buildFactor_arity {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) :
    (buildFactor θ q source).data.arity = source.arity := rfl

@[simp] theorem buildFactor_color {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) :
    (buildFactor θ q source).data.color = source.color := rfl

@[simp] theorem buildFactor_origin {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) :
    (buildFactor θ q source).data.origin = source.origin := rfl

@[simp] theorem buildFactor_table {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) :
    (buildFactor θ q source).data.table = source.table := rfl

theorem buildFactor_taylor_eq {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) (i : Fin source.arity) :
    (buildFactor θ q source).data.taylor i =
      coefficients (buildCodeTaylor θ q (source.rows i)).taylor := by
  simp only [buildFactor, getD_ofFn]

/-- Computable syntax-only bound for all dense expression compilation. -/
def compilationBudget {D p r : ℕ} {K A : Type*}
    (source : FactorSource D p r K A) : ℕ :=
  (List.ofFn (fun i : Fin source.arity =>
    (List.ofFn (fun w : Fin D => 2 * codeWeight (source.rows i w) ^ 2)).sum)).sum

/-- Computable syntax-only bound for all shifted dense rows. -/
def shiftBudget {D p r : ℕ} {K A : Type*}
    (source : FactorSource D p r K A) : ℕ :=
  (List.ofFn (fun i : Fin source.arity =>
    (List.ofFn (fun w : Fin D => 5 * codeLengthBound (source.rows i w) ^ 2)).sum)).sum

theorem buildFactor_compileOps_le_budget {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) :
    (buildFactor θ q source).compileOps ≤ compilationBudget source := by
  simp only [buildFactor, compilationBudget, buildCodeTaylor, Array.toList_ofFn,
    List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro w hw
  exact compileCode_cost (source.rows i w)

theorem buildFactor_shiftOps_le_budget {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) :
    (buildFactor θ q source).shiftOps ≤ shiftBudget source := by
  simp only [buildFactor, shiftBudget, Array.toList_ofFn, List.map_ofFn,
    Function.comp_def, Fin.sum_ofFn]
  apply Finset.sum_le_sum
  intro i hi
  rw [buildCodeTaylor_taylor]
  simp only [buildTaylor, Array.toList_ofFn, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  apply Finset.sum_le_sum
  intro w hw
  exact (buildRow_scalarOps θ q _).trans
    (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (compileCode_lengthBound (source.rows i w)) 2))

theorem buildFactor_compileOps {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) (W : ℕ)
    (hW : ∀ i w, codeWeight (source.rows i w) ≤ W) :
    (buildFactor θ q source).compileOps ≤ 2 * source.arity * D * W ^ 2 := by
  simp only [buildFactor, Array.toList_ofFn, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin source.arity, 2 * D * W ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact buildCodeTaylor_compileOps θ q W _ (hW i)
    _ = _ := by simp; ring

theorem buildFactor_shiftOps {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) (L : ℕ)
    (hL : ∀ i w, codeLengthBound (source.rows i w) ≤ L) :
    (buildFactor θ q source).shiftOps ≤ 5 * source.arity * D * L ^ 2 := by
  simp only [buildFactor, Array.toList_ofFn, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin source.arity, 5 * D * L ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact buildCodeTaylor_scalarOps θ q L _ (hL i)
    _ = _ := by simp; ring

theorem buildFactor_listReads {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (source : FactorSource D p r K A) :
    (buildFactor θ q source).listReads ≤ source.arity * D * (q + 1) ^ 2 := by
  simp only [buildFactor, Array.toList_ofFn, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin source.arity, D * (q + 1) ^ 2 :=
      Finset.sum_le_sum (fun i _ => buildCodeTaylor_listReads θ q (source.rows i))
    _ = _ := by simp; ring

structure FactorBatch (D p q r : ℕ) (K A : Type*) where
  data : List (SubexpProgramBuilder.FactorData D p q r K A)
  compileOps : ℕ
  shiftOps : ℕ
  listReads : ℕ

/-- Traverse the factor list once, sharing every computed record and its
preprocessing counters. The output data feed `SubexpProgramBuilder` directly. -/
def buildFactors {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) : List (FactorSource D p r K A) → FactorBatch D p q r K A
  | [] => ⟨[], 0, 0, 0⟩
  | source :: rest =>
    let first := buildFactor θ q source
    let tail := buildFactors θ q rest
    ⟨first.data :: tail.data, first.compileOps + tail.compileOps,
      first.shiftOps + tail.shiftOps, first.listReads + tail.listReads⟩

def incidenceCount {D p r : ℕ} {K A : Type*}
    (sources : List (FactorSource D p r K A)) : ℕ :=
  (sources.map FactorSource.arity).sum

@[simp] theorem incidenceCount_nil {D p r : ℕ} {K A : Type*} :
    incidenceCount ([] : List (FactorSource D p r K A)) = 0 := rfl

@[simp] theorem incidenceCount_cons {D p r : ℕ} {K A : Type*}
    (source : FactorSource D p r K A) (rest : List (FactorSource D p r K A)) :
    incidenceCount (source :: rest) = source.arity + incidenceCount rest := rfl

@[simp] theorem buildFactors_data {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (sources : List (FactorSource D p r K A)) :
    (buildFactors θ q sources).data = sources.map (fun source => (buildFactor θ q source).data) := by
  induction sources with
  | nil => rfl
  | cons source rest ih => simp only [buildFactors, List.map_cons, ih]

@[simp] theorem buildFactors_length {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (sources : List (FactorSource D p r K A)) :
    (buildFactors θ q sources).data.length = sources.length := by
  rw [buildFactors_data, List.length_map]

theorem buildFactors_map_data {D p r : ℕ} {K A E : Type*} [Semiring A]
    (θ : A) (q : ℕ) (es : List E) (source : E → FactorSource D p r K A) :
    (buildFactors θ q (es.map source)).data =
      es.map (fun e => (buildFactor θ q (source e)).data) := by
  simp only [buildFactors_data, List.map_map, Function.comp_def]

theorem buildFactors_compileOps_le_budget {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (sources : List (FactorSource D p r K A)) :
    (buildFactors θ q sources).compileOps ≤ (sources.map compilationBudget).sum := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    exact Nat.add_le_add (buildFactor_compileOps_le_budget θ q source) ih

theorem buildFactors_shiftOps_le_budget {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (sources : List (FactorSource D p r K A)) :
    (buildFactors θ q sources).shiftOps ≤ (sources.map shiftBudget).sum := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    exact Nat.add_le_add (buildFactor_shiftOps_le_budget θ q source) ih

theorem incidenceCount_le {D p r : ℕ} {K A : Type*}
    (sources : List (FactorSource D p r K A)) (k : ℕ)
    (hk : ∀ source ∈ sources, source.arity ≤ k) :
    incidenceCount sources ≤ sources.length * k :=
  SubexpTableInterpolation.sum_map_le_length_mul sources FactorSource.arity k hk

theorem buildFactors_compileOps {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (sources : List (FactorSource D p r K A)) (W : ℕ)
    (hW : ∀ source ∈ sources, ∀ i w, codeWeight (source.rows i w) ≤ W) :
    (buildFactors θ q sources).compileOps ≤ 2 * incidenceCount sources * D * W ^ 2 := by
  induction sources with
  | nil => simp [buildFactors]
  | cons source rest ih =>
    have hf := buildFactor_compileOps θ q source W (hW source (by simp))
    have ht := ih (fun s hs => hW s (by simp [hs]))
    change (buildFactor θ q source).compileOps + (buildFactors θ q rest).compileOps ≤ _
    rw [incidenceCount_cons]
    calc
      _ ≤ 2 * source.arity * D * W ^ 2 + 2 * incidenceCount rest * D * W ^ 2 :=
        Nat.add_le_add hf ht
      _ = _ := by ring

theorem buildFactors_shiftOps {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (sources : List (FactorSource D p r K A)) (L : ℕ)
    (hL : ∀ source ∈ sources, ∀ i w, codeLengthBound (source.rows i w) ≤ L) :
    (buildFactors θ q sources).shiftOps ≤ 5 * incidenceCount sources * D * L ^ 2 := by
  induction sources with
  | nil => simp [buildFactors]
  | cons source rest ih =>
    have hf := buildFactor_shiftOps θ q source L (hL source (by simp))
    have ht := ih (fun s hs => hL s (by simp [hs]))
    change (buildFactor θ q source).shiftOps + (buildFactors θ q rest).shiftOps ≤ _
    rw [incidenceCount_cons]
    calc
      _ ≤ 5 * source.arity * D * L ^ 2 + 5 * incidenceCount rest * D * L ^ 2 :=
        Nat.add_le_add hf ht
      _ = _ := by ring

theorem buildFactors_listReads {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (sources : List (FactorSource D p r K A)) :
    (buildFactors θ q sources).listReads ≤ incidenceCount sources * D * (q + 1) ^ 2 := by
  induction sources with
  | nil => simp [buildFactors]
  | cons source rest ih =>
    have hf := buildFactor_listReads θ q source
    change (buildFactor θ q source).listReads + (buildFactors θ q rest).listReads ≤ _
    rw [incidenceCount_cons]
    calc
      _ ≤ source.arity * D * (q + 1) ^ 2 + incidenceCount rest * D * (q + 1) ^ 2 :=
        Nat.add_le_add hf ih
      _ = _ := by ring

theorem buildFactors_bounds {D p r : ℕ} {K A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (sources : List (FactorSource D p r K A)) (k W L : ℕ)
    (hk : ∀ source ∈ sources, source.arity ≤ k)
    (hW : ∀ source ∈ sources, ∀ i w, codeWeight (source.rows i w) ≤ W)
    (hL : ∀ source ∈ sources, ∀ i w, codeLengthBound (source.rows i w) ≤ L) :
    (buildFactors θ q sources).compileOps ≤ 2 * sources.length * k * D * W ^ 2 ∧
    (buildFactors θ q sources).shiftOps ≤ 5 * sources.length * k * D * L ^ 2 ∧
    (buildFactors θ q sources).listReads ≤ sources.length * k * D * (q + 1) ^ 2 := by
  have hc := incidenceCount_le sources k hk
  refine ⟨(buildFactors_compileOps θ q sources W hW).trans ?_,
    (buildFactors_shiftOps θ q sources L hL).trans ?_,
    (buildFactors_listReads θ q sources).trans ?_⟩ <;>
    nlinarith [Nat.mul_le_mul_right (D * W ^ 2) (Nat.mul_le_mul_left 2 hc),
      Nat.mul_le_mul_right (D * L ^ 2) (Nat.mul_le_mul_left 5 hc),
      Nat.mul_le_mul_right (D * (q + 1) ^ 2) hc]

section Semantics

noncomputable section

variable {D p q r : ℕ} {K A : Type*} [CommRing A]

/-- The local Taylor identity required by program correctness is a theorem
of the constructor, not a certificate supplied with the input. -/
theorem buildFactor_taylor (θ : A) (q : ℕ) (source : FactorSource D p r K A)
    (i : Fin source.arity) (j : Fin (q + 1)) (w : Fin D) :
    (buildFactor θ q source).data.taylor i j w =
      ((source.rows i w).denote.comp (Polynomial.X + Polynomial.C θ)).coeff j.val := by
  rw [buildFactor_taylor_eq]
  exact coefficients_buildCodeTaylor θ q (source.rows i) j w

/-- Scope-reindexed interface matching the local premise of
`SubexpProgramCorrectness.groupExpr_eq_rowGroup`. Only the denotation of the
input row syntax must be connected to the desired mathematical row. -/
theorem buildFactor_taylor_of_denote {σ : Type*} (θ : A) (q : ℕ)
    (source : FactorSource D p r K A) (ix : Fin source.arity ≃ σ)
    (row : σ → Fin D → Polynomial A)
    (hrow : ∀ i w, (source.rows i w).denote = row (ix i) w)
    (i : Fin source.arity) (j : Fin (q + 1)) (w : Fin D) :
    (buildFactor θ q source).data.taylor i j w =
      ((row (ix i) w).comp (Polynomial.X + Polynomial.C θ)).coeff j.val := by
  rw [buildFactor_taylor, hrow]

theorem argument_buildFactor [Semiring K] (lift : K → A) (θ : A) (q : ℕ)
    (source : FactorSource D p r K A) (x : Fin D → K) (i : Fin source.arity) :
    SubexpProgramBuilder.argument lift (buildFactor θ q source).data x i =
      compileCodeArgument θ (SubexpInputCode.beta lift (source.origin i) x) q (source.rows i) := by
  unfold SubexpProgramBuilder.argument compileCodeArgument
  rw [buildFactor_taylor_eq]
  rfl

theorem argumentValue_buildFactor [Semiring K] (lift : K → A) (θ : A) (q : ℕ)
    (source : FactorSource D p r K A) (x : Fin D → K) (i : Fin source.arity) :
    SubexpProgramBuilder.argumentValue lift (buildFactor θ q source).data x i =
      Counting.rowArgument (fun w => (source.rows i w).denote) θ
        (SubexpInputCode.beta lift (source.origin i) x) q := by
  calc
    _ = SymbolicCost.denote
        (SubexpProgramBuilder.argument lift (buildFactor θ q source).data x i) :=
      (SubexpProgramBuilder.argument_correct lift (buildFactor θ q source).data x i).symm
    _ = _ := by rw [argument_buildFactor, denote_compileCodeArgument]

end

end Semantics

end SubexponentialSAT.SubexpFactorCode

end OAI.Algorithms
