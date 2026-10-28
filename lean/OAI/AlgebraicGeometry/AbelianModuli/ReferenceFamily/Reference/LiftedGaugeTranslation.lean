import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodLiftDisplacements
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualTranslationTrivialization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing

/-! # Lifted Gauge Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

section

/-! Holomorphic trivializations of the native translation cocycle lift
to actual local holomorphic gauges on the vector space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.liftedGauge_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.liftedGauge_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def AlgebraicModel.ReferenceAlgebraicModel.liftedTranslationGauge (a : F.periodData.space)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := F.periodData.space) (M := M.liftedPeriodDomain p) where
  val w := Complex.exp (-(Real.pi : ℂ) * F.form (M.liftedPeriodDisplacement p w).val a) *
    ((g p)⁻¹).val (M.liftedPeriodPoint p w)
  property := by
    have hc := (M.liftedPeriodDisplacement p).isLocallyConstant.comp
      (fun l => Complex.exp (-(Real.pi : ℂ) * F.form l.val a))
    intro w
    exact (contMDiffAt_const.congr_of_eventuallyEq (hc.eventually_eq w)).mul
      ((((g p)⁻¹).val.property.comp (M.liftedPeriodPoint_holomorphic p)) w)

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedTranslationGauge_value (a : F.periodData.space)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (w : M.liftedPeriodDomain p) :
    M.liftedTranslationGauge a g p w =
      Complex.exp (-(Real.pi : ℂ) * F.form (M.liftedPeriodDisplacement p w).val a) /
        (g p).val (M.liftedPeriodPoint p w) :=
  (congrArg (fun t => Complex.exp (-(Real.pi : ℂ) * F.form (M.liftedPeriodDisplacement p w).val a) * t)
    (Holomorphic.GlobalGluing.holomorphicUnit_inverse_value (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.localPeriodDomain p)
      (g p) (M.liftedPeriodPoint p w))).trans (div_eq_mul_inv _ _).symm

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedTranslationGauge_ne_zero (a : F.periodData.space)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (w : M.liftedPeriodDomain p) :
    M.liftedTranslationGauge a g p w ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (g p)⁻¹ (M.liftedPeriodPoint p w))

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedTranslationExponent_change (a : F.periodData.space)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (w : F.periodData.space)
    (hp : w ∈ M.liftedPeriodDomain p) (hr : w ∈ M.liftedPeriodDomain r) :
    Complex.exp (-(Real.pi : ℂ) * F.form (M.liftedPeriodDisplacement r ⟨w, hr⟩).val a) =
      Complex.exp (-(Real.pi : ℂ) * F.form (M.liftedPeriodDisplacement p ⟨w, hp⟩).val a) *
        Complex.exp (M.localTranslationDifference a p r ⟨M.vectorPeriod w, hp, hr⟩) := by
  let d := (M.localPeriodDifference p r ⟨M.vectorPeriod w, hp, hr⟩).val
  let v := (M.liftedPeriodDisplacement p ⟨w, hp⟩).val
  have hlin := congrArg (fun t : Fiber.ReferenceTangent s →ₗ[ℂ] ℂ => t a) (map_sub F.form v d)
  change F.form (v - d) a = F.form v a - F.form d a at hlin
  have hval := (congrArg (fun t => F.form t a) (M.liftedPeriodDisplacement_change p r w hp hr)).trans hlin
  have he : -(Real.pi : ℂ) * F.form (M.liftedPeriodDisplacement r ⟨w, hr⟩).val a =
      -(Real.pi : ℂ) * F.form v a + (Real.pi : ℂ) * F.form d a :=
    (congrArg (fun t : ℂ => -(Real.pi : ℂ) * t) hval).trans (by ring)
  exact (congrArg Complex.exp he).trans (Complex.exp_add _ _)

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedTranslationGauge_compatible (a : F.periodData.space)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (hg : ∀ p r (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)),
      Complex.exp (M.localTranslationDifference a p r q) =
        (g r).val ⟨q.val, q.property.2⟩ / (g p).val ⟨q.val, q.property.1⟩)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (w : F.periodData.space)
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

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.liftedGaugeTranslation_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.liftedGaugeTranslation_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem AlgebraicModel.ReferenceAlgebraicModel.liftedTranslationGauge_translate (a : F.periodData.space)
    (g : ∀ p, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M := M.localPeriodDomain p))ˣ)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (l : F.periodData.periodIntegerLattice)
    (w : M.liftedPeriodDomain p) :
    M.liftedTranslationGauge a g p
        ⟨w.val + l.val, (M.liftedPeriodDomain_translate p l w.val).mpr w.property⟩ *
      Complex.exp ((Real.pi : ℂ) * F.form l.val a) = M.liftedTranslationGauge a g p w := by
  let w' : M.liftedPeriodDomain p :=
    ⟨w.val + l.val, (M.liftedPeriodDomain_translate p l w.val).mpr w.property⟩
  let v := (M.liftedPeriodDisplacement p w).val
  have hlin := congrArg (fun t : Fiber.ReferenceTangent s →ₗ[ℂ] ℂ => t a) (map_add F.form v l.val)
  change F.form (v + l.val) a = F.form v a + F.form l.val a at hlin
  have hval := (congrArg (fun t => F.form t a) (M.liftedPeriodDisplacement_translate p l w)).trans hlin
  have he : -(Real.pi : ℂ) * F.form (M.liftedPeriodDisplacement p w').val a +
      (Real.pi : ℂ) * F.form l.val a = -(Real.pi : ℂ) * F.form v a := by
    rw [hval]
    ring
  have hExp := (Complex.exp_add _ _).symm.trans (congrArg Complex.exp he)
  have hpoint : M.liftedPeriodPoint p w' = M.liftedPeriodPoint p w :=
    Subtype.ext (M.vectorPeriod_add_period l w.val)
  have hd := congrArg (g p).val hpoint
  have hL := M.liftedTranslationGauge_value a g p w'
  have hR := M.liftedTranslationGauge_value a g p w
  have hc := congrArg (fun t : ℂ => t / (g p).val (M.liftedPeriodPoint p w)) hExp
  refine (congrArg (fun t => t * Complex.exp ((Real.pi : ℂ) * F.form l.val a)) hL).trans ?_
  refine Eq.trans ?_ (hc.trans hR.symm)
  rw [hd]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
