import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials

/-! # Test Form Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.TestFormFaithfulness

noncomputable section

/-! Every actual point derivation is a dual-number test, so those tests
detect all algebraic one-forms on a smooth integral complex scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials

variable {R : Type} [CommRing R] [Algebra ℂ R]

theorem pointKaehlerValue_dualTest (x : R →ₐ[ℂ] ℂ) (δ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations x)
    (ω : KaehlerDifferential ℂ R) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap (CommAlgCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation x δ).val) ω) =
      AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue x δ ω := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective ℂ R ω
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | single b a =>
    simp only [Finsupp.linearCombination_single]
    rw [DifferentialNaturality.differentialMap_smul, DifferentialNaturality.differentialMap_D, AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential_smul, AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential_D,
      AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue_smul, AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue_D]
    rfl

attribute [local instance] AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

theorem oneForm_eq_zero_of_dualTests (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (ω : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X)
    (hω : ∀ t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X, AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (ω.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t) = 0) : ω = 0 := by
  apply AlgebraicGeometry.AbelianScheme.TateComparison.FormsAffineLocality.oneForm_eq_zero_of_affineOpens ω
  intro U hU
  classical
  by_cases hUn : Nonempty U
  · let : Nonempty U := hUn
    let R := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
    let : Algebra.Smooth ℂ R := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU
    apply AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.kaehler_eq_zero_of_pointDerivations
    intro x δ
    let f : CommAlgCat.of ℂ R ⟶ AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest := CommAlgCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation x δ).val
    let p := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
    have hn := ω.property (CommAlgCat.of ℂ R) AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest f p
    rw [← pointKaehlerValue_dualTest x δ]
    exact (congrArg AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential hn).trans (hω (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap f ≫ p))
  · have hU0 : U = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (hUn ⟨⟨x, hx⟩⟩).elim
    subst U
    have : Subsingleton (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X ⊥) :=
      inferInstanceAs (Subsingleton Γ(X.left, ⊥))
    exact Subsingleton.elim _ _

theorem oneForms_eq_of_dualTests (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (ω η : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X)
    (h : ∀ t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ X,
      AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (ω.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t) = AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (η.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t)) : ω = η := by
  apply sub_eq_zero.mp
  apply oneForm_eq_zero_of_dualTests X (ω - η)
  intro t
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (ω.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t - η.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t) = 0
  rw [map_sub, h, sub_self]

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.TestFormFaithfulness
