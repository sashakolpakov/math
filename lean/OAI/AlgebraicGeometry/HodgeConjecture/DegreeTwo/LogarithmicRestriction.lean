import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF
import OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogGauge
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence

/-! # Logarithmic Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback

noncomputable section

/-!
# DegreeTwo: actual restriction and relative support of logarithmic Chern classes

Continuous pullback commutes with logarithmic defects and with the genuine
rational Cech-to-singular comparison. If the pulled-back transitions are a
change of frame from the trivial bundle, their singular class vanishes.
Exactness for the actual singular pair then gives a relative lift.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : TopCat.{0}} {I : Type} (f : Y ⟶ X) (U : I → Opens X)

/-- Pull back the actual continuous logarithms on every pairwise intersection. -/
def logarithmPullback (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U) :
    DivisorClass.Chern.LogCech.RationalCech.LogCechCochain Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) :=
  fun a => (l a).comp (CechPullbackF.Constructions.CechPullback.intersectionMap f U a).hom

/-- The pulled-back exponentials satisfy the same transition identity. -/
theorem exponentialCocycle_pullback (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U)
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) :
    DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) (logarithmPullback f U l) := by
  intro a y
  exact h a (CechPullbackF.Constructions.CechPullback.intersectionMap f U a y)

/-- The integer logarithmic defect is preserved by actual continuous pullback. -/
theorem logDefectCocycle_pullback (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U)
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) :
    DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) (logarithmPullback f U l)
      (exponentialCocycle_pullback f U l h) =
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CechPullbackF.Constructions.CechPullback.locallyConstantCochainMap f U) 2 (DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle X U l h) := by
  apply Subtype.ext
  funext a
  apply LocallyConstant.ext
  intro y
  rfl

/-- The actual singular pullback of a logarithmic class is its pulled-back class. -/
theorem logarithmicSingularClass_pullback (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U) (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l) :
    DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) (CechPullbackF.Constructions.CechPullback.pulledCover_covers f U hU)
      (logarithmPullback f U l) (exponentialCocycle_pullback f U l h) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 2
      (DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU l h) := by
  unfold DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass
  rw [logDefectCocycle_pullback]
  exact CechPullbackF.Constructions.CechPullback.classOfCechCocycle_naturality f U hU 2 (DivisorClass.Chern.LogCech.RationalCech.logDefectCocycle X U l h)

/-- Explicit nonzero frames trivializing the pulled-back transitions force zero
 actual singular restriction, without assuming global logarithms of the frames. -/
theorem logarithmicSingularClass_pullback_zero
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U) (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l)
    (g : ∀ i, C(CechPullbackF.Constructions.CechPullback.pulledCover f U i, ℂ)) (hg : ∀ i y, g i y ≠ 0)
    (he : ∀ (a : Fin 2 → I) (y : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechPullbackF.Constructions.CechPullback.pulledCover f U) a),
      Complex.exp (logarithmPullback f U l a y) =
        g (a 1) ⟨y.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (CechPullbackF.Constructions.CechPullback.pulledCover f U) a 1 y.property⟩ /
          g (a 0) ⟨y.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (CechPullbackF.Constructions.CechPullback.pulledCover f U) a 0 y.property⟩) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 2
      (DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU l h) = 0 := by
  rw [← logarithmicSingularClass_pullback]
  calc
    _ = DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) (CechPullbackF.Constructions.CechPullback.pulledCover_covers f U hU) 0
        (DivisorClass.Chern.LogGauge.RationalCech.exponentialCocycle_zero Y (CechPullbackF.Constructions.CechPullback.pulledCover f U)) := by
      apply DivisorClass.Chern.ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) g hg
        (CechPullbackF.Constructions.CechPullback.pulledCover_covers f U hU) 0 (logarithmPullback f U l)
        (DivisorClass.Chern.LogGauge.RationalCech.exponentialCocycle_zero Y (CechPullbackF.Constructions.CechPullback.pulledCover f U))
        (exponentialCocycle_pullback f U l h)
      intro a y
      simpa only [Pi.zero_apply, ContinuousMap.zero_apply, Complex.exp_zero, one_mul]
        using he a y
    _ = 0 := DivisorClass.Chern.LogGauge.RationalCech.logarithmicSingularClass_zero Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) (CechPullbackF.Constructions.CechPullback.pulledCover_covers f U hU)

/-- A logarithmic class trivialized on an actual subspace comes from the genuine
 relative singular cohomology of that pair. -/
theorem logarithmicSingularClass_relative_lift (A : Set X)
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain X U) (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle X U l)
    (g : ∀ i, C(CechPullbackF.Constructions.CechPullback.pulledCover (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) U i, ℂ))
    (hg : ∀ i y, g i y ≠ 0)
    (he : ∀ (a : Fin 2 → I)
        (y : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechPullbackF.Constructions.CechPullback.pulledCover (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) U) a),
      Complex.exp (logarithmPullback (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) U l a y) =
        g (a 1) ⟨y.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 y.property⟩ /
          g (a 0) ⟨y.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 y.property⟩) :
    ∃ c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A 2,
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A 2 c =
        DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU l h := by
  have hz := logarithmicSingularClass_pullback_zero
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) U hU l h g hg he
  have hr : DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass X U hU l h ∈
      LinearMap.range (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A 2).hom := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomology_range_inclusion]
    exact hz
  exact hr

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback
