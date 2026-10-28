import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.TensorSource
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorCompositionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorRefinementValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonBijectivity

/-! # Tensor Comparison Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.TensorComparisonReduction

noncomputable section

/-! Invertibility of the section tensor comparison transports through an open restriction of its source and through an open refinement of its target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem moduleSectionTensorComparisonApp_bijective_of_open_comp
    {X Y Z : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : Z ⟶ Y) (j : Y ⟶ X) [IsOpenImmersion j] (f : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Z, ⊤))
    (hq : q.comp (algebraMap R B) = (a ≫ j).appTop.hom.comp f)
    (hq' : q.comp (algebraMap R B) = a.appTop.hom.comp (j.appTop.hom.comp f))
    (U : X.Opens) (hU : U ≤ j.opensRange)
    (hlocal : Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (j.appTop.hom.comp f)
      ((Scheme.Modules.pullback j).obj M) q hq' (j ⁻¹ᵁ U))) :
    Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ j) f M q hq U) := by
  let F := Module.SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ j) f M q hq U
  let G := Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (j.appTop.hom.comp f) ((Scheme.Modules.pullback j).obj M) q hq' (j ⁻¹ᵁ U)
  let e := OpenPullback.TensorSource.coefficientOpenPullbackSectionEquiv j f M U hU
  let φ := ((Scheme.Modules.pullbackComp a j).hom.app M).app ((a ≫ j) ⁻¹ᵁ U)
  have hφ := (ConcreteCategory.isIso_iff_bijective φ).mp inferInstance
  apply Tensor.ComparisonBijectivity.tensorComparison_bijective_of_pure_square F G e φ.hom hφ hlocal
  intro b x
  exact Module.TensorCompositionValues.moduleSectionTensorComparisonApp_comp a j f M q hq hq' U b x

theorem moduleSectionTensorComparisonApp_bijective_of_open_refine
    {X Y Z : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : X ⟶ Y) [IsOpenImmersion a] (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f) (U : Z.Opens) (hU : g ⁻¹ᵁ U ≤ a.opensRange)
    (hcomp : Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ g) f M (a.appTop.hom.comp q)
      (Coefficient.PullbackRefinement.pullbackCoefficient_compatible_comp a g f q hq) U)) :
    Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq U) := by
  let ρ := (Coefficient.PullbackRefinement.coefficientPullbackRefinementMap a g f M).app (.op U)
  have hρ := (ConcreteCategory.isIso_iff_bijective ρ).mp
    (Coefficient.PullbackRefinement.coefficientPullbackRefinementMap_app_isIso a g f M U hU)
  have he : ρ.hom.comp (Module.SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq U) =
      Module.SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ g) f M (a.appTop.hom.comp q)
        (Coefficient.PullbackRefinement.pullbackCoefficient_compatible_comp a g f q hq) U := by
    apply TensorProduct.ext'
    intro b x
    exact Module.TensorRefinementValues.moduleSectionTensorComparisonApp_refine a g f M q hq U b x
  constructor
  · intro x y hxy
    apply hcomp.injective
    exact (LinearMap.congr_fun he x).symm.trans ((congrArg ρ hxy).trans (LinearMap.congr_fun he y))
  · intro y
    obtain ⟨x, hx⟩ := hcomp.surjective (ρ y)
    exact ⟨x, hρ.injective ((LinearMap.congr_fun he x).trans hx)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.TensorComparisonReduction
