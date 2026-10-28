import OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.Functor

/-! # Flasque Derived -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueDerived

noncomputable section

/-! For flasque complexes, a quasi-isomorphism of actual top sections makes the original adjoint derived comparison bijective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace

local instance flasqueComparisonDerived (X : TopCat.{0}) : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves X) :=
  HasDerivedCategory.standard _

local instance flasqueComparisonExt (X : TopCat.{0}) : HasExt.{1} (ConstantSheafSections.ComplexSheaves X) := HasExt.standard _

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ) (L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℤ)
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℤ)).obj L) (n : ℤ)

def directImageCohomologyMap :=
  Acyclic.Functor.Ext.coefficientDerivedMap (TopologicalSheafPullback.sheafInverseImage f) (ConstantSheafSections.standardConstantSheaf X) (ConstantSheafSections.standardConstantSheaf Y)
    (TopologicalSheafPullback.constantPullbackIso f).inv K L (ImageAdjointNaturality.directImageAdjointComplexMap f α) n

theorem integerHomFunctorComparison_quasiIso_of_sections
    (hα : QuasiIso (ImageAdjointNaturality.integerTopGlobalSectionsPullback f α)) :
    QuasiIso (HomFunctor.Ext.integerHomFunctorComparison (TopologicalSheafPullback.sheafInverseImage f) (TopologicalSheafPullback.constantPullbackIso f).inv
      (ImageAdjointNaturality.directImageAdjointComplexMap f α)) := by
  let H := HomFunctor.Ext.integerHomFunctorComparison (TopologicalSheafPullback.sheafInverseImage f) (TopologicalSheafPullback.constantPullbackIso f).inv
    (ImageAdjointNaturality.directImageAdjointComplexMap f α)
  let eK := ImageAdjointNaturality.integerConstantAdditiveSectionsIso K
  let eL := ImageAdjointNaturality.integerConstantAdditiveSectionsIso L
  have hc : QuasiIso (H ≫ eL.hom) := by
    rw [ImageAdjointNaturality.integerHomFunctorComparison_sections]
    exact quasiIso_comp _ _ (hφ' := hα)
  exact quasiIso_of_comp_right H eL.hom (hφφ' := hc)

variable (b c : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE c]

include b c in
theorem directImageCohomologyMap_bijective_of_flasque
    (hK : ∀ p, TopCat.Sheaf.IsFlasque (K.X p)) (hL : ∀ p, TopCat.Sheaf.IsFlasque (L.X p))
    (hα : QuasiIso (ImageAdjointNaturality.integerTopGlobalSectionsPullback f α)) :
    Function.Bijective (directImageCohomologyMap f K L α n) := by
  apply Acyclic.Functor.Ext.coefficientDerivedMap_bijective_of_acyclic (TopologicalSheafPullback.sheafInverseImage f)
    (ConstantSheafSections.standardConstantSheaf X) (ConstantSheafSections.standardConstantSheaf Y) (TopologicalSheafPullback.constantPullbackIso f).inv K L
    (ImageAdjointNaturality.directImageAdjointComplexMap f α) n b c
  · intro p q
    have := hK p
    exact FlasqueConstantExt.flasqueConstantExt_subsingleton (K.X p) q
  · intro p q
    have := hL p
    exact FlasqueConstantExt.flasqueConstantExt_subsingleton (L.X p) q
  · exact integerHomFunctorComparison_quasiIso_of_sections f K L α hα

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueDerived
