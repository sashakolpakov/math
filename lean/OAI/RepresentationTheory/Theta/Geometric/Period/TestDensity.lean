import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Test Density -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.TestDensity

noncomputable section

/-! Evaluation points detect every function in the actual period-test
ring, and hence determine maps from its reduced spectrum to a separated scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Topology

def periodEvaluationPoint (x y : LinearTheta.BallCoordinates) :
    OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x)) :=
  OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (DifferentialNaturality.functionsAt x)
    ((Pi.evalAlgHom ℂ (fun _ : LinearTheta.BallCoordinates => ℂ) y).comp (DifferentialNaturality.functionsAt x).val)

theorem periodEvaluationPoint_dense (x : LinearTheta.BallCoordinates) :
    DenseRange (fun y => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (periodEvaluationPoint x y)) := by
  let e : LinearTheta.BallCoordinates → PrimeSpectrum (DifferentialNaturality.functionsAt x) :=
    fun y => PrimeSpectrum.comap
      (((Pi.evalAlgHom ℂ (fun _ : LinearTheta.BallCoordinates => ℂ) y).comp (DifferentialNaturality.functionsAt x).val).toRingHom)
      (⊥ : PrimeSpectrum ℂ)
  have hv : PrimeSpectrum.vanishingIdeal (Set.range e) = ⊥ := by
    apply bot_unique
    intro f hf
    change f = 0
    apply Subtype.ext
    funext y
    have h := (PrimeSpectrum.mem_vanishingIdeal _ _).mp hf (e y) ⟨y, rfl⟩
    exact h
  have hd : DenseRange e := by
    rw [denseRange_iff_closure_range, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hv]
    exact PrimeSpectrum.zeroLocus_bot
  exact hd

theorem periodTestMap_ext {X : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsSeparated X.hom]
    (x : LinearTheta.BallCoordinates) (p q : OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x) ⟶ X)
    (h : ∀ y, periodEvaluationPoint x y ≫ p = periodEvaluationPoint x y ≫ q) : p = q := by
  let Z := OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x)
  let : IsReduced (DifferentialNaturality.functionsAt x) :=
    isReduced_of_injective (DifferentialNaturality.functionsAt x).val Subtype.val_injective
  let : IsReduced Z.left := inferInstanceAs (IsReduced (Spec (.of (DifferentialNaturality.functionsAt x))))
  let : IsDominant (equalizer.ι p q).left := by
    constructor
    apply (periodEvaluationPoint_dense x).mono
    rintro _ ⟨y, rfl⟩
    refine ⟨OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (equalizer.lift (periodEvaluationPoint x y) (h y)), ?_⟩
    change OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying
      (equalizer.lift (periodEvaluationPoint x y) (h y) ≫ equalizer.ι p q) = _
    rw [equalizer.lift_ι]
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated X.hom (p.w.trans q.w.symm)
    (equalizer.ι p q).left (congrArg Over.Hom.left (equalizer.condition p q))

end

end OAI.RepresentationTheory.Theta.Geometric.Period.TestDensity
