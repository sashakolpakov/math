import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentKernels
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineOpenSections
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Module Exact Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections

noncomputable section

/-! Actual affine section functors preserve cokernels of quasicoherent modules. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

abbrev sections : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

instance additive : (sections U).Additive where
  map_add := rfl

instance preservesFiniteLimits : PreservesFiniteLimits (sections U) :=
  SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)

include hU

theorem map_epi {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] : Epi ((sections U).map f) := by
  exact Independent.AffineOpenSections.map_epi U hU f

theorem map_exact (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] (hS : S.Exact) :
    (S.map (sections U)).Exact := by
  let F := sections U
  let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
  have hT : T.Exact := (S.exact_iff_exact_image_ι).mp hS
  have hTF : (T.map F).Exact :=
    hT.map_of_mono_of_preservesKernel F inferInstance inferInstance
  let : (Abelian.image S.f).IsQuasicoherent := Independent.QuasicoherentKernels.image S.f
  have : Epi (F.map (Abelian.factorThruImage S.f)) := map_epi U hU _
  let φ : S.map F ⟶ T.map F :=
    { τ₁ := F.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change F.map (Abelian.factorThruImage S.f) ≫ F.map (Abelian.image.ι S.f) = F.map S.f ≫ 𝟙 _
        rw [← F.map_comp, Abelian.image.fac, Category.comp_id] }
  have : Epi φ.τ₁ := (map_epi U hU (Abelian.factorThruImage S.f))
  have : IsIso φ.τ₂ := by change IsIso (𝟙 (F.obj S.X₂)); infer_instance
  have : Mono φ.τ₃ := by change Mono (𝟙 (F.obj S.X₃)); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hTF

theorem preservesCokernel {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) : PreservesColimit (parallelPair f 0) (sections U) := by
  let : (cokernel f).IsQuasicoherent := Independent.QuasicoherentCokernels.quasicoherent f
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
  refine (CokernelCofork.isColimitMapCoconeEquiv _ (sections U)).symm ?_
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : (S.map (sections U)).Exact := map_exact U hU S (ShortComplex.cokernelSequence_exact f)
  have : Epi (S.map (sections U)).g := map_epi U hU (cokernel.π f)
  exact hS.gIsCokernel

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections
