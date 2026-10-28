import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Lean.Util.CollectAxioms

/-! # Bilinear Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearBaseChange

noncomputable section

/-! Scalar extension preserves a finite-dimensional nondegenerate
alternating form and the adjoint equations of its actual linear maps. -/

open scoped TensorProduct

variable {F K V I : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module F V] [Fintype I] [DecidableEq I]
  (b : Module.Basis I F V) (B : LinearMap.BilinForm F V)

theorem bilinearBaseChange_matrix :
    LinearMap.BilinForm.toMatrix (b.baseChange K) (B.baseChange K) =
      (LinearMap.BilinForm.toMatrix b B).map (algebraMap F K) := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
    LinearMap.BilinForm.baseChange_tmul, one_mul, Matrix.map_apply,
    Algebra.algebraMap_eq_smul_one]

include b

theorem bilinearBaseChange_nondegenerate (hB : B.Nondegenerate) :
    (B.baseChange K).Nondegenerate := by
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange K)).mpr
  rw [bilinearBaseChange_matrix b B]
  change ((algebraMap F K).mapMatrix (LinearMap.BilinForm.toMatrix b B)).det ≠ 0
  rw [← RingHom.map_det]
  intro hz
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  apply (algebraMap F K).injective
  exact hz.trans (map_zero (algebraMap F K)).symm

omit [Fintype I] [DecidableEq I] in
theorem bilinearBaseChange_alternating [CharZero K] (hB : B.IsAlt) :
    (B.baseChange K).IsAlt := by
  apply LinearMap.isAlt_iff_eq_neg_flip.mpr
  apply (b.baseChange K).ext
  intro i
  apply (b.baseChange K).ext
  intro j
  change (B.baseChange K) ((b.baseChange K) i) ((b.baseChange K) j) =
    -(B.baseChange K) ((b.baseChange K) j) ((b.baseChange K) i)
  simp only [Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul, one_mul]
  rw [← hB.neg_eq, neg_smul]

omit [Fintype I] [DecidableEq I] in
theorem bilinearBaseChange_adjoint (f g : V →ₗ[F] V)
    (hfg : ∀ x y, B (f x) y = B x (g y)) (x y : K ⊗[F] V) :
    B.baseChange K (f.baseChange K x) y = B.baseChange K x (g.baseChange K y) := by
  have he : (B.baseChange K).compl₁₂ (f.baseChange K) LinearMap.id =
      (B.baseChange K).compl₁₂ LinearMap.id (g.baseChange K) := by
    apply (b.baseChange K).ext
    intro i
    apply (b.baseChange K).ext
    intro j
    change B.baseChange K (f.baseChange K ((b.baseChange K) i)) ((b.baseChange K) j) =
      B.baseChange K ((b.baseChange K) i) (g.baseChange K ((b.baseChange K) j))
    simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      LinearMap.BilinForm.baseChange_tmul, one_mul, hfg]
  exact LinearMap.congr_fun₂ he x y

omit b [Fintype I] [DecidableEq I] in
theorem bilinearCongr_adjoint {W : Type*} [AddCommGroup W] [Module F W]
    (e : V ≃ₗ[F] W) (f g : V →ₗ[F] V) (f' g' : W →ₗ[F] W)
    (hf : f'.comp e.toLinearMap = e.toLinearMap.comp f)
    (hg : g'.comp e.toLinearMap = e.toLinearMap.comp g)
    (hfg : ∀ x y, B (f x) y = B x (g y)) (x y : W) :
    LinearMap.BilinForm.congr e B (f' x) y = LinearMap.BilinForm.congr e B x (g' y) := by
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  have hfx : f' (e x) = e (f x) := LinearMap.congr_fun hf x
  have hgy : g' (e y) = e (g y) := LinearMap.congr_fun hg y
  rw [hfx, hgy]
  simp only [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply]
  exact hfg x y

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearBaseChange
