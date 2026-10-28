import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleGenerators
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Submodule Grading -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.SubmoduleGrading.GradedModules

noncomputable section

/-! Homogeneous submodules inherit genuine internal decompositions. -/

open DirectSum

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {δ : Type w} [DecidableEq δ]
variable (ℳ : δ → Submodule R M) [Decomposition ℳ] (P : Submodule R M)

def submoduleGrading (d : δ) : Submodule R P := (ℳ d).comap P.subtype

def submoduleGradedInclusion : (⨁ d, submoduleGrading ℳ P d) →ₗ[R] ⨁ d, ℳ d :=
  DirectSum.lmap (fun d =>
    (P.subtype.comp (submoduleGrading ℳ P d).subtype).codRestrict (ℳ d) (fun x => x.property))

omit [Decomposition ℳ] in
theorem submoduleGradedInclusion_sum :
    (DirectSum.coeLinearMap ℳ).comp (submoduleGradedInclusion ℳ P) =
      P.subtype.comp (DirectSum.coeLinearMap (submoduleGrading ℳ P)) := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, submoduleGradedInclusion, DirectSum.lmap_lof,
    DirectSum.coeLinearMap_lof]
  rfl

theorem submoduleGrading_sum_injective :
    Function.Injective (DirectSum.coeLinearMap (submoduleGrading ℳ P)) := by
  intro x y h
  have hsum : DirectSum.coeLinearMap ℳ (submoduleGradedInclusion ℳ P x) =
      DirectSum.coeLinearMap ℳ (submoduleGradedInclusion ℳ P y) := by
    exact (LinearMap.congr_fun (submoduleGradedInclusion_sum ℳ P) x).trans
      ((congrArg P.subtype h).trans (LinearMap.congr_fun (submoduleGradedInclusion_sum ℳ P) y).symm)
  have hbase : submoduleGradedInclusion ℳ P x = submoduleGradedInclusion ℳ P y :=
    (DirectSum.decomposeLinearEquiv ℳ).symm.injective hsum
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ⨁ e, ℳ e => (z d).val) hbase

theorem submoduleGrading_iSup_eq_top (hP : P.IsHomogeneous ℳ) :
    (⨆ d, submoduleGrading ℳ P d) = ⊤ := by
  classical
  apply top_unique
  intro x _
  have hx : x = ∑ d ∈ (DirectSum.decompose ℳ x.val).support,
      (⟨(DirectSum.decompose ℳ x.val d).val, hP d x.property⟩ : P) := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using (DirectSum.sum_support_decompose ℳ x.val).symm
  rw [hx]
  apply Submodule.sum_mem
  intro d _
  apply (le_iSup (submoduleGrading ℳ P) d)
  exact (DirectSum.decompose ℳ x.val d).property

theorem submoduleGrading_sum_surjective (hP : P.IsHomogeneous ℳ) :
    Function.Surjective (DirectSum.coeLinearMap (submoduleGrading ℳ P)) := by
  rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap]
  exact submoduleGrading_iSup_eq_top ℳ P hP

@[instance_reducible]
def homogeneousSubmoduleDecomposition (hP : P.IsHomogeneous ℳ) :
    DirectSum.Decomposition (submoduleGrading ℳ P) := by
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap (submoduleGrading ℳ P))
    ⟨submoduleGrading_sum_injective ℳ P, submoduleGrading_sum_surjective ℳ P hP⟩
  exact DirectSum.Decomposition.ofLinearMap _ e.symm.toLinearMap
    (by apply LinearMap.ext; intro x; exact e.apply_symm_apply x)
    (by apply LinearMap.ext; intro x; exact e.symm_apply_apply x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.SubmoduleGrading.GradedModules
