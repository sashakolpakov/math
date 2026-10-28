import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntegrationDerivedClass
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ConstantNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.SheafNaturality

/-! # Derived Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.DerivedNormalization.Integration

noncomputable section

/-! The original projective integration Betti class is identified with the
original standard-constant smooth de Rham derived class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance projectiveBettiPointContractible : StronglyLocallyContractibleSpace (TopCat.of V.analyticSpace) :=
  IntegrationDerivedClass.projectiveIntegrationLocallyContractible V
local instance projectiveBettiPointMetrizable : MetrizableSpace (TopCat.of V.analyticSpace) :=
  IntegrationDerivedClass.projectivePointIntegrationMetrizable V
local instance projectiveBettiHasDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of V.analyticSpace)) :=
  HasDerivedCategory.standard _
local instance projectiveBettiHasExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of V.analyticSpace)) :=
  hasExt_of_hasDerivedCategory _

theorem projective_betti_derivedClass (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (TopCat.of V.analyticSpace) n
      ((V.deRhamBettiIso n).hom (V.deRhamClass n a)) =
      Filtered.DerivedInclusion.Hodge.smoothGlobalDerivedClass V.analyticModel V.analyticSpace n a.val a.property ≫
        (Betti.Smooth.ConstantNormalization.Integration.smoothStandardResolutionIso V.analyticModel V.analyticSpace).inv⟦(n : ℤ)⟧' := by
  erw [Derived.SheafNaturality.singularDerivedConstantLinearEquiv_factor,
    ExtDerivedPullback.locallyConstantExtDerivedEquiv_apply, IntegrationDerivedClass.projective_integration_derivedClass]
  erw [Category.assoc, ← CategoryTheory.Functor.map_comp, Betti.Smooth.ConstantNormalization.Integration.smoothStandardResolutionIso_inverse]
  rfl

local instance projectiveNormalizationIntegral : AlgebraicGeometry.IsIntegral V.toOver.left := V.property
local instance projectiveNormalizationSmooth : AlgebraicGeometry.Smooth V.toOver.hom := V.presentation.smooth

theorem projective_standardResolutionIso_hom :
    (Betti.Smooth.ConstantNormalization.Integration.smoothStandardResolutionIso V.analyticModel V.analyticSpace).hom =
      (Analytic.De.analyticDeRhamResolutionIso V.toOver).hom := by
  rw [Betti.Smooth.ConstantNormalization.Integration.smoothStandardResolutionIso_hom]
  rfl

theorem projective_standardResolutionIso :
    Betti.Smooth.ConstantNormalization.Integration.smoothStandardResolutionIso V.analyticModel V.analyticSpace =
      Analytic.De.analyticDeRhamResolutionIso V.toOver :=
  Iso.ext (projective_standardResolutionIso_hom V)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.DerivedNormalization.Integration
