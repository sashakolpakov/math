import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.PivotCokernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Rank
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MatrixMinors
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientRetraction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ExactKernels

/-! # Flat Matrix Pivot Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatMatrixPivotCover.Grassmannian

noncomputable section

/-! Every finite matrix with flat cokernel over a local ring admits a coordinate pivot chart satisfying the actual polynomial residual equations. -/

open _root_.Module

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {μ : Type v} {ν : Type w} [Fintype μ] [Fintype ν]
variable [DecidableEq μ] [DecidableEq ν]

theorem local_flat_matrix_pivot_cover (A : Matrix ν μ R)
    [Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range)] :
    ∃ (q : ℕ) (a : Fin q → μ) (b : Fin q → ν),
      Function.Injective a ∧ Function.Injective b ∧
      IsUnit (A.submatrix b a).det ∧ MatrixPivot.PivotCokernel.Grassmannian.fullPivotResidual A a b = 0 := by
  classical
  let f := Matrix.toLin' A
  let : Module.Free R ((ν → R) ⧸ f.range) := Module.free_of_flat_of_isLocalRing
  let : Module.Flat R f.range := Presentations.Flat.ExactKernels.flat_of_exact_flat_quotient f.range.subtype f.range.mkQ
    f.range.subtype_injective f.range.mkQ_surjective (LinearMap.exact_subtype_mkQ f.range)
  let : Module.FinitePresentation R f.range := Module.finitePresentation_of_projective_of_exact
    f.range.subtype f.range.mkQ f.range.subtype_injective f.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ f.range)
  let v : μ → f.range := f.rangeRestrict ∘ Pi.basisFun R μ
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun R μ).span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr f.surjective_rangeRestrict
  obtain ⟨κ, a, B, hB⟩ := Module.exists_basis_of_span_of_flat v hv
  have ha : Function.Injective a := by
    intro i j hij
    apply B.injective
    rw [hB i, hB j, hij]
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let q := Fintype.card κ
  let e : κ ≃ Fin q := Fintype.equivFin κ
  let C := B.reindex e
  let a' := a ∘ e.symm
  let E := A.submatrix id a'
  have hC (i : Fin q) : (C i).val = fun j => A j (a' i) := by
    rw [Basis.reindex_apply, hB]
    funext j
    simp [v, a', f, Matrix.toLin'_apply, Matrix.col_apply]
  have hE : Matrix.toLin' E = f.range.subtype.comp C.equivFun.symm.toLinearMap := by
    apply (Pi.basisFun R (Fin q)).ext
    intro i
    have hCi : C.equivFun.symm (Pi.single i 1) = C i := by
      apply C.equivFun.injective
      simp
    funext j
    rw [Pi.basisFun_apply]
    change Matrix.toLin' E (Pi.single i 1) j = (C.equivFun.symm (Pi.single i 1)).val j
    rw [hCi]
    simpa only [E, Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.submatrix_apply, id_eq] using congrFun (hC i).symm j
  obtain ⟨r, hr⟩ := Projective.QuotientRetraction.exists_projective_quotient_retraction f.range
  let L := LinearMap.toMatrix' (C.equivFun.toLinearMap.comp r)
  have hLE : L * E = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' (C.equivFun.toLinearMap.comp r))).comp (Matrix.toLin' E) = _
    rw [Matrix.toLin'_toMatrix', hE]
    apply LinearMap.ext
    intro x
    change C.equivFun (r ((C.equivFun.symm x).val)) = x
    have hrx := LinearMap.congr_fun hr (C.equivFun.symm x)
    change r ((C.equivFun.symm x).val) = C.equivFun.symm x at hrx
    rw [hrx, LinearEquiv.apply_symm_apply]
  obtain ⟨b, hb, hminor⟩ := MatrixMinors.Grassmannian.local_split_matrix_unit_row_minor E L hLE
  have hminor' : IsUnit (A.submatrix b a').det := hminor
  let F := LinearMap.toMatrix' (C.equivFun.toLinearMap.comp f.rangeRestrict)
  have hF : A = E * F := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hE]
    change f = (f.range.subtype.comp C.equivFun.symm.toLinearMap).comp
      (Matrix.toLin' (LinearMap.toMatrix' (C.equivFun.toLinearMap.comp f.rangeRestrict)))
    rw [Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    change f x = (C.equivFun.symm (C.equivFun (f.rangeRestrict x))).val
    rw [LinearEquiv.symm_apply_apply]
    rfl
  exact ⟨q, a', b, ha.comp e.symm.injective, hb, hminor',
    MatrixPivot.PivotCokernel.Grassmannian.fullPivotResidual_zero_of_factorization A a' b hminor' F hF⟩

theorem local_matrix_cokernel_flat_iff_pivot (A : Matrix ν μ R) :
    Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range) ↔
      ∃ (q : ℕ) (a : Fin q → μ) (b : Fin q → ν),
        Function.Injective a ∧ Function.Injective b ∧
        IsUnit (A.submatrix b a).det ∧ MatrixPivot.PivotCokernel.Grassmannian.fullPivotResidual A a b = 0 := by
  classical
  constructor
  · intro h
    let := h
    exact local_flat_matrix_pivot_cover A
  · rintro ⟨q, a, b, _, _, hu, hz⟩
    let : Module.Free R ((ν → R) ⧸ (Matrix.toLin' A).range) :=
      Module.Free.of_equiv (MatrixPivot.PivotCokernel.Grassmannian.fullMatrixPivotCokernelEquiv A a b hu hz).symm
    infer_instance

theorem local_flat_matrix_pivot_cover_rank (A : Matrix ν μ R)
    [Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range)] (r : ℕ)
    (hr : Module.finrank R ((ν → R) ⧸ (Matrix.toLin' A).range) = r) :
    ∃ (q : ℕ) (a : Fin q → μ) (b : Fin q → ν),
      Function.Injective a ∧ Function.Injective b ∧
      IsUnit (A.submatrix b a).det ∧ MatrixPivot.PivotCokernel.Grassmannian.fullPivotResidual A a b = 0 ∧ q + r = Fintype.card ν := by
  classical
  obtain ⟨q, a, b, ha, hb, hu, hz⟩ := local_flat_matrix_pivot_cover A
  have hq : q ≤ Fintype.card ν := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective b hb
  have hbcard : Fintype.card {j : ν // j ∈ Set.range b} = q := by
    rw [← Fintype.card_congr (Equiv.ofInjective b hb), Fintype.card_fin]
  have he := (MatrixPivot.PivotCokernel.Grassmannian.fullMatrixPivotCokernelEquiv A a b hu hz).finrank_eq
  rw [hr, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, hbcard] at he
  exact ⟨q, a, b, ha, hb, hu, hz, by omega⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatMatrixPivotCover.Grassmannian
