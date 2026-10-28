import OAI.RepresentationTheory.Theta.Geometric.Reference.ArchimedeanGroup
import OAI.Geometry.ComplexBall.QuotientAtlas

/-! # Arithmetic Ball -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The exact arithmetic orbit quotient has its actual quotient
covering, and injects into the original PEL moduli points. -/

open scoped _root_.Manifold

open OAI.Geometry.ComplexBall.QuotientAtlas.Arithmetic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

abbrev Data.ActiveHeckeThetaData.ArithmeticBallQuotient := MulAction.orbitRel.Quotient D.archimedeanArithmeticSubgroup D.domain

def Data.ActiveHeckeThetaData.arithmeticBallProjection : D.domain → D.ArithmeticBallQuotient := Quotient.mk _

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.arithmeticBallProjection_covering : IsCoveringMap D.arithmeticBallProjection := by
  let : IsCancelSMul D.archimedeanArithmeticSubgroup D.domain := D.archimedeanArithmetic_free hg hc hgood hdegree
  let : ProperlyDiscontinuousSMul D.archimedeanArithmeticSubgroup D.domain :=
    D.archimedeanArithmetic_properlyDiscontinuous hg hc hgood hdegree
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap

theorem Data.ActiveHeckeThetaData.arithmeticBallProjection_surjective : Function.Surjective D.arithmeticBallProjection :=
  Quotient.mk_surjective

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.referenceModuliMap_iff_archimedeanOrbit (x y : D.domain) :
    D.referenceModuliMap hg x = D.referenceModuliMap hg y ↔
      MulAction.orbitRel D.archimedeanArithmeticSubgroup D.domain x y := by
  constructor
  · intro h
    obtain ⟨g, hfinite, hy⟩ := (D.referenceModuliMap_orbits hg hc hgood hdegree x y).mp h
    apply (MulAction.orbitRel D.archimedeanArithmeticSubgroup D.domain).symm
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap D.pel.reference.b D.pel.reference.μ g, ⟨g, hfinite, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (Period.Ne.rationalPeriodPerm_on_ball D.pel.reference.b D.pel.reference.μ g x).symm.trans hy.symm
  · intro h
    obtain ⟨g, hg'⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    obtain ⟨a, ha, he⟩ := g.property
    apply Eq.symm
    apply (D.referenceModuliMap_orbits hg hc hgood hdegree y x).mpr
    refine ⟨a, ha, ?_⟩
    rw [Data.ActiveHeckeThetaData.periodMap, Period.Ne.rationalPeriodPerm_on_ball D.pel.reference.b D.pel.reference.μ a y, he]
    exact (congrArg Subtype.val hg').symm

def Data.ActiveHeckeThetaData.arithmeticModuliMap : D.ArithmeticBallQuotient → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace :=
  Quotient.lift (D.referenceModuliMap hg) (fun x y h =>
    (D.referenceModuliMap_iff_archimedeanOrbit hg hc hgood hdegree x y).mpr h)

theorem Data.ActiveHeckeThetaData.arithmeticModuliMap_projection (x : D.domain) :
    D.arithmeticModuliMap hg hc hgood hdegree (D.arithmeticBallProjection x) = D.referenceModuliMap hg x := rfl

theorem Data.ActiveHeckeThetaData.arithmeticModuliMap_injective : Function.Injective (D.arithmeticModuliMap hg hc hgood hdegree) := by
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      intro h
      exact Quotient.sound ((D.referenceModuliMap_iff_archimedeanOrbit hg hc hgood hdegree x y).mp h)

@[instance_reducible] def Data.ActiveHeckeThetaData.arithmeticBallAtlas : ChartedSpace LinearTheta.BallCoordinates D.ArithmeticBallQuotient :=
  letI : IsCancelSMul D.archimedeanArithmeticSubgroup D.domain := D.archimedeanArithmetic_free hg hc hgood hdegree
  letI : ProperlyDiscontinuousSMul D.archimedeanArithmeticSubgroup D.domain :=
    D.archimedeanArithmetic_properlyDiscontinuous hg hc hgood hdegree
  Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientAtlas _ hg.reference_admissible.2.2.2.1 D.archimedeanArithmeticSubgroup

theorem Data.ActiveHeckeThetaData.arithmeticBallAtlas_isManifold :
    letI := D.arithmeticBallAtlas hg hc hgood hdegree
    IsManifold 𝓘(ℂ, LinearTheta.BallCoordinates) 1 D.ArithmeticBallQuotient := by
  let : IsCancelSMul D.archimedeanArithmeticSubgroup D.domain := D.archimedeanArithmetic_free hg hc hgood hdegree
  let : ProperlyDiscontinuousSMul D.archimedeanArithmeticSubgroup D.domain :=
    D.archimedeanArithmetic_properlyDiscontinuous hg hc hgood hdegree
  exact Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientAtlas_isManifold _ hg.reference_admissible.2.2.2.1 D.archimedeanArithmeticSubgroup

end

end OAI.RepresentationTheory.Theta.Geometric
