import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet

/-! # Period Jet Differentials -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials

noncomputable section

/-! The universal period differential is exactly evaluation on the actual dual-number tangent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] TrivSqZeroExt.algebraBase

local instance : IsScalarTower ℂ (DualNumber ℂ) ℂ := by
  constructor
  intro a b c
  change (a * b.fst) * c = a * (b.fst * c)
  exact mul_assoc _ _ _

def dualDerivation : Derivation ℂ (DualNumber ℂ) ℂ where
  toFun := TrivSqZeroExt.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_one_eq_zero' := rfl
  leibniz' a b := by
    change a.fst * b.snd + a.snd * b.fst = a.fst * b.snd + b.fst * a.snd
    ring

def dualDifferential : KaehlerDifferential ℂ (DualNumber ℂ) →ₗ[ℂ] ℂ :=
  dualDerivation.liftKaehlerDifferential.restrictScalars ℂ

theorem dualDifferential_D (a : DualNumber ℂ) :
    dualDifferential (KaehlerDifferential.D ℂ (DualNumber ℂ) a) = a.snd :=
  dualDerivation.liftKaehlerDifferential_comp_D a

theorem dualDifferential_smul (a : DualNumber ℂ) (form : KaehlerDifferential ℂ (DualNumber ℂ)) :
    dualDifferential (a • form) = a.fst * dualDifferential form :=
  dualDerivation.liftKaehlerDifferential.map_smul a form

theorem periodDifferential_firstOrder (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    (form : KaehlerDifferential ℂ (RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x)) :
    dualDifferential (AbelianScheme.TateComparison.FormConstants.differentialMap (CommAlgCat.ofHom (PeriodJets.firstOrderEvaluation x u)) form) =
      RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential x form u := by
  obtain ⟨r, rfl⟩ := KaehlerDifferential.linearCombination_surjective ℂ (RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x) form
  induction r using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_apply]
  | add r t hr ht => simp only [map_add, add_apply, hr, ht]
  | single b a =>
    simp only [Finsupp.linearCombination_single, RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential_smul, RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential_D,
      smul_apply, smul_eq_mul]
    let f : RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x ⟶ PeriodJet.dualTest := CommAlgCat.ofHom (PeriodJets.firstOrderEvaluation x u)
    have hs := RepresentationTheory.Theta.Geometric.DifferentialNaturality.differentialMap_smul f a (KaehlerDifferential.D ℂ (RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x) b)
    have hd := RepresentationTheory.Theta.Geometric.DifferentialNaturality.differentialMap_D f b
    exact ((congrArg dualDifferential hs).trans (dualDifferential_smul _ _)).trans
      (congrArg ((PeriodJets.firstOrderEvaluation x u a).fst * ·)
        ((congrArg dualDifferential hd).trans (dualDifferential_D _)))

theorem formInPeriodCoordinates_firstOrder {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (p : AbelianScheme.TateComparison.FormConstants.affineComplexTest (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) ⟶ X) (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    RepresentationTheory.Theta.Geometric.DifferentialNaturality.formInPeriodCoordinates x p form u =
      dualDifferential (form.val PeriodJet.dualTest (PeriodJet.firstOrderPoint x u p)) := by
  have h := form.property (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) PeriodJet.dualTest
    (CommAlgCat.ofHom (PeriodJets.firstOrderEvaluation x u)) p
  exact (periodDifferential_firstOrder x u (form.val (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) p)).symm.trans
    (congrArg dualDifferential h)

theorem formInPeriodCoordinates_firstOrderLift {X U : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (i : U ⟶ X) (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    (p : AbelianScheme.TateComparison.FormConstants.affineComplexTest (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) ⟶ X) (l : AbelianScheme.TateComparison.FormConstants.affineComplexTest PeriodJet.dualTest ⟶ U)
    (hl : l ≫ i = PeriodJet.firstOrderPoint x u p) (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    RepresentationTheory.Theta.Geometric.DifferentialNaturality.formInPeriodCoordinates x p form u =
      dualDifferential ((AbelianScheme.TateComparison.FormConstants.formsPullback i form).val PeriodJet.dualTest l) := by
  rw [formInPeriodCoordinates_firstOrder, ← hl]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials
