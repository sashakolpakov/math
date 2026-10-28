import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.TranslationSub
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.Translation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass
import OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

/-! # Dual Translation Trivialization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Integral dual-lattice parameters have explicit holomorphic gauges.
Consequently the actual translation class descends to the constructed
dual period torus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.dualTranslation_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.dualTranslation_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.dualTranslation_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

def AlgebraicModel.ReferenceAlgebraicModel.localLinearTranslationLog (a : F.periodData.space)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M := M.localPeriodDomain p) where
  val q := (Real.pi : ℂ) * F.form a (M.localPeriodLift p q.val)
  property := by
    intro q
    have hw : ContMDiffAt 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, F.periodData.space) ∞
        (fun t : M.localPeriodDomain p => M.localPeriodLift p t.val) q :=
      (M.localPeriodLift_contMDiffAt p q.val q.property).comp q
        (contMDiff_subtype_val (I := 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (n := ∞) q)
    have hp : ContDiff ℂ ∞ (fun w : F.periodData.space => (Real.pi : ℂ) * F.form a w) :=
      contDiff_const.mul (F.form a).toContinuousLinearMap.contDiff
    exact hp.contMDiff.contMDiffAt.comp q hw

theorem AlgebraicModel.ReferenceAlgebraicModel.localLinearTranslationLog_difference (a : F.periodData.space)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    M.localLinearTranslationLog a r ⟨q.val, q.property.2⟩ -
      M.localLinearTranslationLog a p ⟨q.val, q.property.1⟩ =
        (Real.pi : ℂ) * F.form a (M.localPeriodDifference p r q).val := by
  have hd := (congrArg (fun t : ℂ => (Real.pi : ℂ) * t)
    (map_sub (F.form a) (M.localPeriodLift r q.val) (M.localPeriodLift p q.val))).trans (mul_sub _ _ _)
  exact hd.symm.trans (congrArg (fun w => (Real.pi : ℂ) * F.form a w)
    (M.localPeriodDifference_value p r q).symm)

omit M in
theorem AlgebraicModel.ReferenceAlgebraicModel.dualTranslation_exponential (a : F.dualLattice) (l : F.periodData.periodIntegerLattice) :
    Complex.exp ((Real.pi : ℂ) * F.form l.val a.val) =
      Complex.exp ((Real.pi : ℂ) * F.form a.val l.val) := by
  obtain ⟨m, hm⟩ := Submodule.mem_one.mp (a.property l.val l.property)
  have h := (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter_eq_one_iff F.form F.hermitian a.val l.val).mpr ⟨m, hm.symm⟩
  change Complex.exp ((Real.pi : ℂ) * (F.form a.val l.val - F.form l.val a.val)) = 1 at h
  have he := (congrArg Complex.exp (mul_sub (Real.pi : ℂ) (F.form a.val l.val) (F.form l.val a.val))).symm
  have hq := (Complex.exp_sub ((Real.pi : ℂ) * F.form a.val l.val)
    ((Real.pi : ℂ) * F.form l.val a.val)).symm.trans (he.trans h)
  have hm := (div_eq_iff (Complex.exp_ne_zero ((Real.pi : ℂ) * F.form l.val a.val))).mp hq
  exact ((one_mul _).symm.trans hm.symm)

theorem AlgebraicModel.ReferenceAlgebraicModel.dualTranslation_local_gauge (a : F.dualLattice)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    Complex.exp (M.localTranslationDifference a.val p r q) =
      (DivisorClass.Chern.Holomorphic.Exponential.holomorphicExpUnit (M.localLinearTranslationLog a.val r)).val ⟨q.val, q.property.2⟩ /
        (DivisorClass.Chern.Holomorphic.Exponential.holomorphicExpUnit (M.localLinearTranslationLog a.val p)).val ⟨q.val, q.property.1⟩ := by
  exact (AlgebraicModel.ReferenceAlgebraicModel.dualTranslation_exponential a (M.localPeriodDifference p r q)).trans
    ((congrArg Complex.exp (M.localLinearTranslationLog_difference a.val p r q).symm).trans
      (Complex.exp_sub _ _))

theorem AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicClass_dual_zero (a : F.dualLattice) :
    M.translationHolomorphicClass a.val = 0 := by
  have hU : ∀ x, ∃ i, x ∈ M.localPeriodDomain i := fun x => ⟨x, M.mem_localPeriodDomain x⟩
  have hz := Intrinsic.HolomorphicIsoClass.holomorphicUnitCech_class_zero_of_trivialization (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) M.localPeriodDomain hU
    (M.translationUnitCech a.val) (M.translationUnitCech_closed a.val)
    (fun i => DivisorClass.Chern.Holomorphic.Exponential.holomorphicExpUnit (M.localLinearTranslationLog a.val i))
    (fun b q => (M.translationUnitCech_value a.val b q).trans
      (M.dualTranslation_local_gauge a (b 0) (b 1)
        ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
          AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩))
  exact (M.translationUnitCech_class a.val).symm.trans hz

def AlgebraicModel.ReferenceAlgebraicModel.dualTorusHolomorphicHom : (F.dualPeriodData hP).periodTorus →+
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  QuotientAddGroup.lift F.dualLattice.toAddSubgroup M.translationHolomorphicHom
    (fun a ha => M.translationHolomorphicClass_dual_zero ⟨a, ha⟩)

theorem AlgebraicModel.ReferenceAlgebraicModel.dualTorusHolomorphicHom_mk (a : F.periodData.space) :
    M.dualTorusHolomorphicHom (QuotientAddGroup.mk a) = M.translationHolomorphicClass a := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
