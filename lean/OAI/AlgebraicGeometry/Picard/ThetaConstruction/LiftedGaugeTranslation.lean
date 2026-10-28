import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodLiftDisplacements
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DualTranslationTrivialization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing

/-! # Lifted Gauge Translation -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

section

/-! Holomorphic trivializations of the native translation cocycle lift
to actual local holomorphic gauges on the vector space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.liftedGauge_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.liftedGauge_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def PeriodModel.Geometric.AlgebraicPeriodModel.liftedTranslationGauge (a : DefinitionsIntegral.Tangent dim)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := (ProjectivePeriodData.Geometric.projectivePeriodData T).space) (M := M.liftedPeriodDomain p) where
  val w := Complex.exp (-(Real.pi : ℂ) * T.riemannForm (M.liftedPeriodDisplacement p w).val a) *
    ((g p)⁻¹).val (M.liftedPeriodPoint p w)
  property := by
    have hc := (M.liftedPeriodDisplacement p).isLocallyConstant.comp
      (fun l => Complex.exp (-(Real.pi : ℂ) * T.riemannForm l.val a))
    intro w
    exact (contMDiffAt_const.congr_of_eventuallyEq (hc.eventually_eq w)).mul
      ((((g p)⁻¹).val.property.comp (M.liftedPeriodPoint_holomorphic p)) w)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedTranslationGauge_value (a : DefinitionsIntegral.Tangent dim)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (w : M.liftedPeriodDomain p) :
    M.liftedTranslationGauge a g p w =
      Complex.exp (-(Real.pi : ℂ) * T.riemannForm (M.liftedPeriodDisplacement p w).val a) /
        (g p).val (M.liftedPeriodPoint p w) :=
  (congrArg (fun t => Complex.exp (-(Real.pi : ℂ) * T.riemannForm (M.liftedPeriodDisplacement p w).val a) * t)
    (AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing.holomorphicUnit_inverse_value (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.localPeriodDomain p)
      (g p) (M.liftedPeriodPoint p w))).trans (div_eq_mul_inv _ _).symm

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedTranslationGauge_ne_zero (a : DefinitionsIntegral.Tangent dim)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (w : M.liftedPeriodDomain p) :
    M.liftedTranslationGauge a g p w ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (g p)⁻¹ (M.liftedPeriodPoint p w))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedTranslationExponent_change (a : DefinitionsIntegral.Tangent dim)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (w : DefinitionsIntegral.Tangent dim)
    (hp : w ∈ M.liftedPeriodDomain p) (hr : w ∈ M.liftedPeriodDomain r) :
    Complex.exp (-(Real.pi : ℂ) * T.riemannForm (M.liftedPeriodDisplacement r ⟨w, hr⟩).val a) =
      Complex.exp (-(Real.pi : ℂ) * T.riemannForm (M.liftedPeriodDisplacement p ⟨w, hp⟩).val a) *
        Complex.exp (M.localTranslationDifference a p r ⟨M.vectorPeriod w, hp, hr⟩) := by
  let d := (M.localPeriodDifference p r ⟨M.vectorPeriod w, hp, hr⟩).val
  let v := (M.liftedPeriodDisplacement p ⟨w, hp⟩).val
  have hlin := congrArg (fun t : DefinitionsIntegral.Tangent dim →ₗ[ℂ] ℂ => t a) (map_sub T.riemannForm v d)
  change T.riemannForm (v - d) a = T.riemannForm v a - T.riemannForm d a at hlin
  have hval := (congrArg (fun t => T.riemannForm t a) (M.liftedPeriodDisplacement_change p r w hp hr)).trans hlin
  have he : -(Real.pi : ℂ) * T.riemannForm (M.liftedPeriodDisplacement r ⟨w, hr⟩).val a =
      -(Real.pi : ℂ) * T.riemannForm v a + (Real.pi : ℂ) * T.riemannForm d a :=
    (congrArg (fun t : ℂ => -(Real.pi : ℂ) * t) hval).trans (by ring)
  exact (congrArg Complex.exp he).trans (Complex.exp_add _ _)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedTranslationGauge_compatible (a : DefinitionsIntegral.Tangent dim)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (hg : ∀ p r (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)),
      Complex.exp (M.localTranslationDifference a p r q) =
        (g r).val ⟨q.val, q.property.2⟩ / (g p).val ⟨q.val, q.property.1⟩)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (w : DefinitionsIntegral.Tangent dim)
    (hp : w ∈ M.liftedPeriodDomain p) (hr : w ∈ M.liftedPeriodDomain r) :
    M.liftedTranslationGauge a g p ⟨w, hp⟩ = M.liftedTranslationGauge a g r ⟨w, hr⟩ := by
  have hc := M.liftedTranslationExponent_change a p r w hp hr
  have hχ := hg p r ⟨M.vectorPeriod w, hp, hr⟩
  have hR := M.liftedTranslationGauge_value a g r ⟨w, hr⟩
  have hL := M.liftedTranslationGauge_value a g p ⟨w, hp⟩
  have hn := DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (g r) (M.liftedPeriodPoint r ⟨w, hr⟩)
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [hc, hχ]
  field_simp
  rfl

end

/-! The lifted local gauges have the exact original inverse translation
character under every integral period. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.liftedGaugeTranslation_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.liftedGaugeTranslation_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.liftedTranslationGauge_translate (a : DefinitionsIntegral.Tangent dim)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice)
    (w : M.liftedPeriodDomain p) :
    M.liftedTranslationGauge a g p
        ⟨w.val + l.val, (M.liftedPeriodDomain_translate p l w.val).mpr w.property⟩ *
      Complex.exp ((Real.pi : ℂ) * T.riemannForm l.val a) = M.liftedTranslationGauge a g p w := by
  let w' : M.liftedPeriodDomain p :=
    ⟨w.val + l.val, (M.liftedPeriodDomain_translate p l w.val).mpr w.property⟩
  let v := (M.liftedPeriodDisplacement p w).val
  have hlin := congrArg (fun t : DefinitionsIntegral.Tangent dim →ₗ[ℂ] ℂ => t a) (map_add T.riemannForm v l.val)
  change T.riemannForm (v + l.val) a = T.riemannForm v a + T.riemannForm l.val a at hlin
  have hval := (congrArg (fun t => T.riemannForm t a) (M.liftedPeriodDisplacement_translate p l w)).trans hlin
  have he : -(Real.pi : ℂ) * T.riemannForm (M.liftedPeriodDisplacement p w').val a +
      (Real.pi : ℂ) * T.riemannForm l.val a = -(Real.pi : ℂ) * T.riemannForm v a := by
    rw [hval]
    ring
  have hExp := (Complex.exp_add _ _).symm.trans (congrArg Complex.exp he)
  have hpoint : M.liftedPeriodPoint p w' = M.liftedPeriodPoint p w :=
    Subtype.ext (M.vectorPeriod_add_period l w.val)
  have hd := congrArg (g p).val hpoint
  have hL := M.liftedTranslationGauge_value a g p w'
  have hR := M.liftedTranslationGauge_value a g p w
  have hc := congrArg (fun t : ℂ => t / (g p).val (M.liftedPeriodPoint p w)) hExp
  refine (congrArg (fun t => t * Complex.exp ((Real.pi : ℂ) * T.riemannForm l.val a)) hL).trans ?_
  refine Eq.trans ?_ (hc.trans hR.symm)
  rw [hd]
  ring

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
