import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationDolbeaultSub
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualLe
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass
import OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

/-! # Dual Translation Trivialization -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Integral dual-lattice parameters have explicit holomorphic gauges.
Consequently the actual translation class descends to the constructed
dual period torus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.dualTranslation_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.dualTranslation_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.dualTranslation_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

def PeriodModel.Geometric.AlgebraicPeriodModel.localLinearTranslationLog (a : DefinitionsIntegral.Tangent dim)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.localPeriodDomain p) where
  val q := (Real.pi : ℂ) * T.riemannForm a (M.localPeriodLift p q.val)
  property := by
    intro q
    have hw : ContMDiffAt 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) ∞
        (fun t : M.localPeriodDomain p => M.localPeriodLift p t.val) q :=
      (M.localPeriodLift_contMDiffAt p q.val q.property).comp q
        (contMDiff_subtype_val (I := 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (n := ∞) q)
    let ell : (ProjectivePeriodData.Geometric.projectivePeriodData T).space →L[ℂ] ℂ := (T.riemannForm a).toContinuousLinearMap
    have hp : ContDiff ℂ ∞ (fun w : (ProjectivePeriodData.Geometric.projectivePeriodData T).space => (Real.pi : ℂ) * T.riemannForm a w) :=
      contDiff_const.mul ell.contDiff
    exact hp.contMDiff.contMDiffAt.comp q hw

theorem PeriodModel.Geometric.AlgebraicPeriodModel.localLinearTranslationLog_difference (a : DefinitionsIntegral.Tangent dim)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    M.localLinearTranslationLog a r ⟨q.val, q.property.2⟩ -
      M.localLinearTranslationLog a p ⟨q.val, q.property.1⟩ =
        (Real.pi : ℂ) * T.riemannForm a (M.localPeriodDifference p r q).val := by
  have hd := (congrArg (fun t : ℂ => (Real.pi : ℂ) * t)
    (map_sub (T.riemannForm a) (M.localPeriodLift r q.val) (M.localPeriodLift p q.val))).trans (mul_sub _ _ _)
  exact hd.symm.trans (congrArg (fun w => (Real.pi : ℂ) * T.riemannForm a w)
    (M.localPeriodDifference_value p r q).symm)

omit M in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.dualTranslation_exponential (a : T.integralDualLattice) (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) :
    Complex.exp ((Real.pi : ℂ) * T.riemannForm l.val a.val) =
      Complex.exp ((Real.pi : ℂ) * T.riemannForm a.val l.val) := by
  obtain ⟨m, hm⟩ := Submodule.mem_one.mp (a.property l.val l.property)
  have h := (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter_eq_one_iff T.riemannForm T.hermitian a.val l.val).mpr ⟨m, hm.symm⟩
  change Complex.exp ((Real.pi : ℂ) * (T.riemannForm a.val l.val - T.riemannForm l.val a.val)) = 1 at h
  have he := (congrArg Complex.exp (mul_sub (Real.pi : ℂ) (T.riemannForm a.val l.val) (T.riemannForm l.val a.val))).symm
  have hq := (Complex.exp_sub ((Real.pi : ℂ) * T.riemannForm a.val l.val)
    ((Real.pi : ℂ) * T.riemannForm l.val a.val)).symm.trans (he.trans h)
  have hm := (div_eq_iff (Complex.exp_ne_zero ((Real.pi : ℂ) * T.riemannForm l.val a.val))).mp hq
  exact ((one_mul _).symm.trans hm.symm)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.dualTranslation_local_gauge (a : T.integralDualLattice)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    Complex.exp (M.localTranslationDifference a.val p r q) =
      (DivisorClass.Chern.Holomorphic.Exponential.holomorphicExpUnit (M.localLinearTranslationLog a.val r)).val ⟨q.val, q.property.2⟩ /
        (DivisorClass.Chern.Holomorphic.Exponential.holomorphicExpUnit (M.localLinearTranslationLog a.val p)).val ⟨q.val, q.property.1⟩ := by
  exact (PeriodModel.Geometric.AlgebraicPeriodModel.dualTranslation_exponential a (M.localPeriodDifference p r q)).trans
    ((congrArg Complex.exp (M.localLinearTranslationLog_difference a.val p r q).symm).trans
      (Complex.exp_sub _ _))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicClass_dual_zero (a : T.integralDualLattice) :
    M.translationHolomorphicClass a.val = 0 := by
  have hU : ∀ x, ∃ i, x ∈ M.localPeriodDomain i := fun x => ⟨x, M.mem_localPeriodDomain x⟩
  have hz := AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass.holomorphicUnitCech_class_zero_of_trivialization (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) M.localPeriodDomain hU
    (M.translationUnitCech a.val) (M.translationUnitCech_closed a.val)
    (fun i => DivisorClass.Chern.Holomorphic.Exponential.holomorphicExpUnit (M.localLinearTranslationLog a.val i))
    (fun b q => (M.translationUnitCech_value a.val b q).trans
      (M.dualTranslation_local_gauge a (b 0) (b 1)
        ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
          AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩))
  exact (M.translationUnitCech_class a.val).symm.trans hz

def PeriodModel.Geometric.AlgebraicPeriodModel.dualTorusHolomorphicHom : T.integralDualPeriodData.periodTorus →+
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  QuotientAddGroup.lift T.integralDualLattice.toAddSubgroup M.translationHolomorphicHom
    (fun a ha => M.translationHolomorphicClass_dual_zero ⟨a, ha⟩)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.dualTorusHolomorphicHom_mk (a : DefinitionsIntegral.Tangent dim) :
    M.dualTorusHolomorphicHom (QuotientAddGroup.mk a) = M.translationHolomorphicClass a := rfl

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
