import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointGlobalEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SpectrumLineBundleFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis

/-! # Line Bundle Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.LineBundleEvaluation

noncomputable section

/-! A frame of the actual line-bundle fiber gives a coefficient-linear
evaluation functional on global sections. Its kernel is precisely the
sections vanishing at the rational point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)
variable (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)

def rationalLineBundleSectionValue (a : Line.Bundles.structureModule X ⟶ L.sheaf) : K :=
  PointGlobalEvaluation.rationalPointGlobalEvaluation (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) (Category.id_comp _)
    (Frame.Coordinates.structureModuleEndValue (Spec (.of K))
      (Ample.LineBundles.pullbackSection x a ≫ (Local.SpectrumLineBundleFrames.localSpectrumLineBundleIso (L.pullback x)).hom))

theorem rationalLineBundleSectionValue_add (a b : Line.Bundles.structureModule X ⟶ L.sheaf) :
    rationalLineBundleSectionValue L x (a + b) =
      rationalLineBundleSectionValue L x a + rationalLineBundleSectionValue L x b := by
  unfold rationalLineBundleSectionValue
  erw [Section.NonvanishingAddition.pullbackSection_add, Preadditive.add_comp, map_add]
  rfl

include hx in
theorem rationalLineBundleSectionValue_scalar (r : K) (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    rationalLineBundleSectionValue L x (Scalar.SectionValues.scalarSection (Coefficient.ModulePresheaf.schemeCoefficientMap p r) a) =
      r * rationalLineBundleSectionValue L x a := by
  let E := Local.SpectrumLineBundleFrames.localSpectrumLineBundleIso (L.pullback x)
  let ε := PointGlobalEvaluation.rationalPointGlobalEvaluation (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) (Category.id_comp _)
  have h := congrArg ε (Family.FramedSectionEvaluation.familyFramedSectionValue_scalar p L x hx E
    ((Scheme.ΓSpecIso (.of K)).inv r) a)
  rw [map_mul] at h
  have hc : ε ((Scheme.ΓSpecIso (.of K)).inv r) = r :=
    PointGlobalEvaluation.rationalPointGlobalEvaluation_coefficient (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K)))
      (Category.id_comp _) r
  rw [hc] at h
  exact h

theorem rationalLineBundleSectionValue_eq_zero (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    rationalLineBundleSectionValue L x a = 0 ↔
      x (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing a := by
  unfold rationalLineBundleSectionValue
  rw [PointGlobalEvaluation.rationalPointGlobalEvaluation_eq_zero, ← Scalar.Nonvanishing.sectionNonvanishing_scalar,
    Ample.Powers.sectionNonvanishing_comp_iso, LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange x L a]
  rfl

def rationalLineBundleEvaluation :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf →ₗ[K] K where
  toFun v := rationalLineBundleSectionValue L x
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm v)
  map_add' v w := by
    erw [map_add]
    exact rationalLineBundleSectionValue_add L x _ _
  map_smul' r v := by
    have he : (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm (r • v) =
        Scalar.SectionValues.scalarSection (Coefficient.ModulePresheaf.schemeCoefficientMap p r)
          ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm v) := by
      apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).injective
      erw [AddEquiv.apply_symm_apply, Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar,
        AddEquiv.apply_symm_apply]
    rw [he]
    exact rationalLineBundleSectionValue_scalar p L x hx r _

theorem rationalLineBundleEvaluation_eq_zero
    (v : (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf) :
    rationalLineBundleEvaluation p L x hx v = 0 ↔
      x (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing
        ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf).symm v) :=
  rationalLineBundleSectionValue_eq_zero L x _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.LineBundleEvaluation
