import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientTransformations

/-! # Section Coefficient Transform -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionCoefficientTransform

noncomputable section

/-! Actual section combinations commute with arbitrary scheme pullback,
with the coefficient homomorphism composed by the map on global functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u v w
variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

def sectionPullbackAddHom :
    (Line.Bundles.structureModule X ⟶ M) →+ (Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj M) where
  toFun s := Ample.LineBundles.pullbackSection f s
  map_zero' := by simp only [Ample.LineBundles.pullbackSection, Functor.map_zero, CategoryTheory.Limits.comp_zero]
  map_add' := Section.NonvanishingAddition.pullbackSection_add f

theorem coefficientSectionCombination_pullback {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) {ι : Type v} (s : ι → (Line.Bundles.structureModule X ⟶ M)) (a : ι →₀ R) :
    Ample.LineBundles.pullbackSection f (Section.CoefficientTransformations.coefficientSectionCombination c M s a) =
      Section.CoefficientTransformations.coefficientSectionCombination (f.appTop.hom.comp c) ((Scheme.Modules.pullback f).obj M)
        (fun i => Ample.LineBundles.pullbackSection f (s i)) a := by
  rw [Section.CoefficientTransformations.coefficientSectionCombination_sum, Section.CoefficientTransformations.coefficientSectionCombination_sum]
  change sectionPullbackAddHom f M (∑ i ∈ a.support, Scalar.SectionValues.scalarSection (c (a i)) (s i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Coefficient.RingSectionBasis.pullbackSection_scalarSection f (c (a i)) (s i)

theorem transformSectionFamily_pullback {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) {ι : Type v} {κ : Type w}
    (s : ι → (Line.Bundles.structureModule X ⟶ M)) (T : (κ →₀ R) →ₗ[R] (ι →₀ R)) (j : κ) :
    Ample.LineBundles.pullbackSection f (Section.CoefficientTransformations.transformSectionFamily c M s T j) =
      Section.CoefficientTransformations.transformSectionFamily (f.appTop.hom.comp c) ((Scheme.Modules.pullback f).obj M)
        (fun i => Ample.LineBundles.pullbackSection f (s i)) T j :=
  coefficientSectionCombination_pullback f M c s _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionCoefficientTransform
