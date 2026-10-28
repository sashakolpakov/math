import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankLowerOpen

/-! # Kernel Dimension Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelDimensionOpen

noncomputable section

/-! The locus where the kernel of a finite matrix has fiber dimension at most a given bound is open and commutes with base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

omit [Fintype ν] [DecidableEq ν] in
theorem field_matrix_kernel_dimension_add_rank {K : Type u} [Field K] (A : Matrix ν μ K) :
    Module.finrank K (Matrix.toLin' A).ker + A.rank = Fintype.card μ := by
  change Module.finrank K (Matrix.toLin' A).ker +
    Module.finrank K (Matrix.toLin' A).range = Fintype.card μ
  rw [Nat.add_comm]
  exact (LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)).trans
    (Module.finrank_fintype_fun_eq_card K)

omit [Fintype ν] [DecidableEq ν] in
theorem field_matrix_kernel_dimension_le_iff_rank {K : Type u} [Field K]
    (A : Matrix ν μ K) (d : ℕ) :
    Module.finrank K (Matrix.toLin' A).ker ≤ d ↔ Fintype.card μ - d ≤ A.rank := by
  have := field_matrix_kernel_dimension_add_rank A
  omega

def matrixKernelDimensionOpen {X : Scheme.{u}} (A : Matrix ν μ Γ(X, ⊤)) (d : ℕ) : X.Opens :=
  RankLowerOpen.matrixRankLowerOpen A (Fintype.card μ - d)

omit [Fintype ν] [DecidableEq μ] [DecidableEq ν] in
theorem matrixKernelDimensionOpen_preimage {X Y : Scheme.{u}} (c : Y ⟶ X)
    (A : Matrix ν μ Γ(X, ⊤)) (d : ℕ) :
    c ⁻¹ᵁ matrixKernelDimensionOpen A d = matrixKernelDimensionOpen (A.map c.appTop.hom) d :=
  RankLowerOpen.matrixRankLowerOpen_preimage c A _

theorem matrixKernelDimensionOpen_field_point {X : Scheme.{u}} {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ X) (A : Matrix ν μ Γ(X, ⊤)) (d : ℕ) :
    (letI : Field Γ(Spec (.of K), ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
        (Field.toIsField K)).toField;
      Set.range c ⊆ (matrixKernelDimensionOpen A d : Set X) ↔
        Module.finrank Γ(Spec (.of K), ⊤) (Matrix.toLin' (A.map c.appTop.hom)).ker ≤ d) := by
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  exact (RankLowerOpen.matrixRankLowerOpen_field_point c A _).trans
    (field_matrix_kernel_dimension_le_iff_rank _ d).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelDimensionOpen
