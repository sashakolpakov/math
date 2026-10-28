import OAI.AlgebraicGeometry.Comparison.Betti.Projective.DerivedNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredDerivedImage

/-! # Holomorphic Filtered Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicFilteredImage.Integration

noncomputable section

/-! On a smooth integral projective variety, the original holomorphic
truncation image is exactly the original Betti classes of closed filtered forms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredDerivedImage.Hodge

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance projectiveFilteredPointContractible : StronglyLocallyContractibleSpace (TopCat.of V.analyticSpace) :=
  IntegrationDerivedClass.projectiveIntegrationLocallyContractible V
local instance projectiveFilteredPointMetrizable : MetrizableSpace (TopCat.of V.analyticSpace) :=
  IntegrationDerivedClass.projectivePointIntegrationMetrizable V
local instance projectiveFilteredHasDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of V.analyticSpace)) :=
  HasDerivedCategory.standard _

theorem projective_closed_derivedClass_iff (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) (b : V.complexCohomology n) :
    Filtered.DerivedInclusion.Hodge.smoothGlobalDerivedClass V.analyticModel V.analyticSpace n a.val a.property =
      Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (TopCat.of V.analyticSpace) n b ≫
        (Smooth.ConstantNormalization.Integration.smoothStandardResolutionIso V.analyticModel V.analyticSpace).hom⟦(n : ℤ)⟧' ↔
      (V.deRhamBettiIso n).hom (V.deRhamClass n a) = b := by
  let e := (shiftFunctor (DerivedCategory (ConstantSheafSections.ComplexSheaves (TopCat.of V.analyticSpace))) (n : ℤ)).mapIso
    (Smooth.ConstantNormalization.Integration.smoothStandardResolutionIso V.analyticModel V.analyticSpace)
  constructor
  · intro h
    apply (Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (TopCat.of V.analyticSpace) n).injective
    erw [DerivedNormalization.Integration.projective_betti_derivedClass, h, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  · intro h
    have hh := congrArg (Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (TopCat.of V.analyticSpace) n) h
    erw [DerivedNormalization.Integration.projective_betti_derivedClass] at hh
    exact e.comp_inv_eq.mp hh

theorem projective_holomorphicTruncation_image_iff (n : ℕ) (r : ℤ) (b : V.complexCohomology n) :
    (∃ c : (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of V.analyticSpace)) 0).obj
        (ConstantSheafSections.standardConstantSheaf (TopCat.of V.analyticSpace)) ⟶
      (DerivedCategory.Q.obj ((Holomorphic.FilteredDerivedImage.Hodge.holomorphicTruncatedComplexNat V.analyticModel V.analyticSpace r).extend
        (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧,
      c ≫ (Holomorphic.FilteredDerivedImage.Hodge.holomorphicTruncationToSmoothDerived V.analyticModel V.analyticSpace r)⟦(n : ℤ)⟧' =
        Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (TopCat.of V.analyticSpace) n b ≫
          (Smooth.ConstantNormalization.Integration.smoothStandardResolutionIso V.analyticModel V.analyticSpace).hom⟦(n : ℤ)⟧') ↔
    ∃ (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n),
      a.val ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration V.analyticModel V.analyticSpace n r ∧
        (V.deRhamBettiIso n).hom (V.deRhamClass n a) = b := by
  rw [Holomorphic.FilteredDerivedImage.Hodge.holomorphicTruncation_image_iff_closed_filtered]
  constructor
  · rintro ⟨a, ha, hab⟩
    exact ⟨⟨a.val, ha⟩, a.property, (projective_closed_derivedClass_iff V n ⟨a.val, ha⟩ b).1 hab⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨⟨a.val, ha⟩, a.property, (projective_closed_derivedClass_iff V n a b).2 hab⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicFilteredImage.Integration
