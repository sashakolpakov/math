import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixFlatExtension

/-! # Rational Subspace Density -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RationalSubspaceDensity.Construction

noncomputable section

/-! Real scalar spans of rational subspaces lie in their ordinary
topological closure. This supplies rational approximation inside a
linear system defined over a subfield of the reals. -/

open scoped Classical
open Set

def rationalClosureRealSubmodule
    {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℚ E] [IsScalarTower ℚ ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [ContinuousConstSMul ℚ E]
    (W : Submodule ℚ E) : Submodule ℝ E where
  carrier := closure (W : Set E)
  zero_mem' := subset_closure W.zero_mem
  add_mem' hx hy := W.topologicalClosure.add_mem hx hy
  smul_mem' c x hx := by
    have hc : IsClosed {r : ℝ | r • x ∈ closure (W : Set E)} :=
      isClosed_closure.preimage (continuous_id.smul continuous_const)
    apply hc.closure_subset_iff.mpr ?_ (Rat.denseRange_cast c)
    rintro _ ⟨q, rfl⟩
    change (q : ℝ) • x ∈ W.topologicalClosure
    rw [Rat.cast_smul_eq_qsmul]
    exact W.topologicalClosure.smul_mem q hx

theorem real_span_subset_rational_closure
    {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℚ E] [IsScalarTower ℚ ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [ContinuousConstSMul ℚ E] (W : Submodule ℚ E) :
    (Submodule.span ℝ (W : Set E) : Set E) ⊆ closure (W : Set E) := by
  exact (Submodule.span_le.mpr (show (W : Set E) ⊆ rationalClosureRealSubmodule W from subset_closure))

def matrixCoefficientRationalMap {k : Type} [Field k] [CharZero k] {n : ℕ}
    (v : k →+* ℝ) : Matrix (Fin n) (Fin n) k →ₗ[ℚ] Matrix (Fin n) (Fin n) ℝ where
  toFun Q := Q.map v
  map_add' Q R := by ext i j; exact map_add v _ _
  map_smul' c Q := by
    ext i j
    change v (c • Q i j) = c • v (Q i j)
    simpa only [Algebra.smul_def] using map_rat_smul v c (Q i j)

theorem matrixSubspaceExtension_subset_closure
    {k : Type} [Field k] [CharZero k] [Algebra k ℝ] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    (MatrixFlatExtension.Construction.matrixSubspaceExtension (K := ℝ) W : Set (Matrix (Fin n) (Fin n) ℝ)) ⊆
      closure ((fun Q : Matrix (Fin n) (Fin n) k => Q.map (algebraMap k ℝ)) '' W) := by
  let V := (W.restrictScalars ℚ).map (matrixCoefficientRationalMap (algebraMap k ℝ))
  have hV : (V : Set (Matrix (Fin n) (Fin n) ℝ)) =
      (fun Q : Matrix (Fin n) (Fin n) k => Q.map (algebraMap k ℝ)) '' W := rfl
  rw [MatrixFlatExtension.Construction.matrixSubspaceExtension_eq_span, ← hV]
  exact real_span_subset_rational_closure V

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RationalSubspaceDensity.Construction
