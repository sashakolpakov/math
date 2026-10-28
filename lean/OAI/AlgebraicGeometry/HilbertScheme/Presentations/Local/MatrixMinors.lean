import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Cokernel
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Matrix Minors -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MatrixMinors.Grassmannian

noncomputable section

/-! Surjective matrices over local rings have invertible coordinate minors. -/

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [Fintype ν]
variable [DecidableEq ι] [DecidableEq ν]

theorem local_surjective_matrix_unit_minor (A : Matrix ι ν R)
    (hA : Function.Surjective (Matrix.toLin' A)) :
    ∃ a : ι → ν, Function.Injective a ∧ IsUnit (A.submatrix id a).det := by
  classical
  let v : ν → (ι → R) := Matrix.toLin' A ∘ Pi.basisFun R ν
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun R ν).span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hA
  obtain ⟨κ, a, B, hB⟩ := Module.exists_basis_of_span_of_flat v hv
  have ha : Function.Injective a := by
    intro i j hij
    apply B.injective
    rw [hB i, hB j, hij]
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let e : κ ≃ ι := Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fintype_fun_eq_card])
  let C := B.reindex e
  let a' := a ∘ e.symm
  have hC (i : ι) : C i = fun j => A j (a' i) := by
    rw [Module.Basis.reindex_apply, hB]
    funext j
    simp [v, a', Matrix.toLin'_apply, Matrix.col_apply]
  have hM : Matrix.toLin' (A.submatrix id a') = C.equivFun.symm.toLinearMap := by
    apply (Pi.basisFun R ι).ext
    intro i
    have hCi : C.equivFun.symm (Pi.single i 1) = C i := by
      apply C.equivFun.injective
      simp
    funext j
    simpa only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.submatrix_apply, id_eq, LinearEquiv.coe_coe, hCi] using congrFun (hC i).symm j
  have hunit : IsUnit (C.equivFun.symm.toLinearMap : Module.End R (ι → R)) := by
    refine ⟨⟨C.equivFun.symm.toLinearMap, C.equivFun.toLinearMap, ?_, ?_⟩, rfl⟩
    · apply LinearMap.ext
      intro x
      exact C.equivFun.symm_apply_apply x
    · apply LinearMap.ext
      intro x
      exact C.equivFun.apply_symm_apply x
  rw [← hM] at hunit
  exact ⟨a', ha.comp e.symm.injective,
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_toLin'_iff.mp hunit)⟩

theorem local_split_matrix_unit_row_minor (A : Matrix ν ι R) (L : Matrix ι ν R)
    (hLA : L * A = 1) :
    ∃ a : ι → ν, Function.Injective a ∧ IsUnit (A.submatrix a id).det := by
  have htranspose : A.transpose * L.transpose = 1 := by
    rw [← Matrix.transpose_mul, hLA, Matrix.transpose_one]
  have hsurj : Function.Surjective (Matrix.toLin' A.transpose) := by
    intro x
    refine ⟨Matrix.toLin' L.transpose x, ?_⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, htranspose, Matrix.toLin'_one, LinearMap.id_apply]
  obtain ⟨a, ha, hdet⟩ := local_surjective_matrix_unit_minor A.transpose hsurj
  refine ⟨a, ha, ?_⟩
  have ht : A.transpose.submatrix id a = (A.submatrix a id).transpose := rfl
  rwa [ht, Matrix.det_transpose] at hdet

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MatrixMinors.Grassmannian
