import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatMatrixPivotCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Transitions

/-! # Fixed Rank Cokernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FixedRankCokernel.Grassmannian

noncomputable section

/-! A finite matrix over a local ring has flat cokernel of the prescribed rank
exactly when it lies in one of the coordinate pivot charts of that size. -/

universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {ι : Type v} {μ : Type w} {ν : Type z}
variable [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

theorem local_cokernel_flat_fixed_rank_iff (A : Matrix ν μ R) :
    (Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range) ∧
      Module.finrank R ((ν → R) ⧸ (Matrix.toLin' A).range) + Fintype.card ι = Fintype.card ν) ↔
    ∃ (a : ι ↪ μ) (b : ι ↪ ν), IsUnit (A.submatrix b a).det ∧ MatrixPivot.PivotCokernel.Grassmannian.fullPivotResidual A a b = 0 := by
  classical
  constructor
  · rintro ⟨hflat, hr⟩
    let := hflat
    obtain ⟨q, a, b, ha, hb, hu, hz, hq⟩ :=
      FlatMatrixPivotCover.Grassmannian.local_flat_matrix_pivot_cover_rank A (Module.finrank R ((ν → R) ⧸ (Matrix.toLin' A).range)) rfl
    have hqi : q = Fintype.card ι := by omega
    let e : ι ≃ Fin q := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hqi])
    let a' : ι ↪ μ := ⟨a ∘ e, ha.comp e.injective⟩
    let b' : ι ↪ ν := ⟨b ∘ e, hb.comp e.injective⟩
    have hu' : IsUnit (A.submatrix b' a').det := by
      change IsUnit ((A.submatrix b a).submatrix e e).det
      rwa [Matrix.det_submatrix_equiv_self]
    refine ⟨a', b', hu', ?_⟩
    let E := MatrixPivot.PivotCokernel.Grassmannian.normalizedPivotColumns A a b
    let F := A.submatrix b id
    have hA : A = E * F := MatrixPivot.PivotCokernel.Grassmannian.fullPivotResidual_factorization A a b hu hz
    apply MatrixPivot.Transitions.Grassmannian.fullPivotResidual_zero_of_width_factorization A (E.submatrix id e) (F.submatrix e id) _ a' b' hu'
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    exact hA
  · rintro ⟨a, b, hu, hz⟩
    let e := MatrixPivot.PivotCokernel.Grassmannian.fullMatrixPivotCokernelEquiv A a b hu hz
    have hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range) := Module.Flat.of_linearEquiv e
    have hc : Fintype.card {j : ν // j ∈ Set.range b} = Fintype.card ι :=
      (Fintype.card_congr (Equiv.ofInjective b b.injective)).symm
    have hle : Fintype.card ι ≤ Fintype.card ν := Fintype.card_le_of_injective b b.injective
    have hr := e.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, hc] at hr
    exact ⟨hflat, by omega⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FixedRankCokernel.Grassmannian
