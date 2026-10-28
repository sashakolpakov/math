import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Refinement

/-! # Log Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinement

noncomputable section

/-!
# ChernClass: logarithmic Chern classes are invariant under further cover refinement

The actual integral defect restricts naturally, and the rational singular
comparison preserves that restriction. New logarithms of the same transitions
give the same class as the restricted ones.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I J : Type} (X : TopCat.{0})
variable (U : I → Opens X) (V : J → Opens X) (r : J → I) (hr : ∀ j, V j ≤ U (r j))

/-- The restriction of continuous logarithms to a refinement. -/
abbrev refineLogCech (l : LogCech.RationalCech.LogCechCochain X U) : LogCech.RationalCech.LogCechCochain X V :=
  Rational.Cech.RationalCech.cechRefinementMap (LogCech.RationalCech.continuousComplexPresheaf X) U V r hr 1 l

/-- The exponential transition identity survives actual restriction. -/
theorem exponentialCocycle_refinement (l : LogCech.RationalCech.LogCechCochain X U)
    (h : LogCech.RationalCech.ExponentialCocycle X U l) :
    LogCech.RationalCech.ExponentialCocycle X V (refineLogCech X U V r hr l) := by
  intro a x
  exact h (r ∘ a) ⟨x.val, Rational.Cech.RationalCech.cechIntersection_refinement_le U V r hr a x.property⟩

/-- The integral logarithmic defect, after rationalization, commutes with refinement. -/
theorem logDefectCech_refinement (l : LogCech.RationalCech.LogCechCochain X U)
    (h : LogCech.RationalCech.ExponentialCocycle X U l) :
    LogCech.RationalCech.logDefectCech X V (refineLogCech X U V r hr l)
        (exponentialCocycle_refinement X U V r hr l h) =
      Rational.Cech.RationalCech.cechRefinementMap (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr 2 (LogCech.RationalCech.logDefectCech X U l h) := by
  apply LogCech.RationalCech.periodCechMap_injective X V 2
  rw [Cech.Refinement.RationalCech.cechCoefficientMap_refinement, LogCech.RationalCech.periodMap_logDefectCech,
    LogCech.RationalCech.periodMap_logDefectCech, Rational.Cech.RationalCech.cechRefinementMap_delta]

/-- The refined logarithmic cocycle is the image under the actual cochain map. -/
theorem logDefectCocycle_refinement (l : LogCech.RationalCech.LogCechCochain X U)
    (h : LogCech.RationalCech.ExponentialCocycle X U l) :
    LogCech.RationalCech.logDefectCocycle X V (refineLogCech X U V r hr l)
        (exponentialCocycle_refinement X U V r hr l h) =
      AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Rational.Cech.RationalCech.cechRefinement (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr) 2
        (LogCech.RationalCech.logDefectCocycle X U l h) := by
  apply Subtype.ext
  exact logDefectCech_refinement X U V r hr l h

/-- Refining the cover leaves the rational singular class unchanged. -/
theorem logarithmicSingularClass_refinement
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ x : X, ∃ j, x ∈ V j)
    (l : LogCech.RationalCech.LogCechCochain X U) (h : LogCech.RationalCech.ExponentialCocycle X U l) :
    LogCech.RationalCech.logarithmicSingularClass X V hV (refineLogCech X U V r hr l)
        (exponentialCocycle_refinement X U V r hr l h) =
      LogCech.RationalCech.logarithmicSingularClass X U hU l h := by
  unfold LogCech.RationalCech.logarithmicSingularClass
  rw [logDefectCocycle_refinement]
  exact Singular.Refinement.RationalCech.singularClassOfCechCocycle_refinement X U V r hr hU hV 2 (LogCech.RationalCech.logDefectCocycle X U l h)

/-- One may choose new logarithms on the finer cover without changing the class. -/
theorem logarithmicSingularClass_refinement_of_exp_eq
    (hU : ∀ x : X, ∃ i, x ∈ U i) (hV : ∀ x : X, ∃ j, x ∈ V j)
    (l : LogCech.RationalCech.LogCechCochain X U) (h : LogCech.RationalCech.ExponentialCocycle X U l)
    (l' : LogCech.RationalCech.LogCechCochain X V) (h' : LogCech.RationalCech.ExponentialCocycle X V l')
    (he : ∀ (a : Fin 2 → J) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a),
      Complex.exp (l' a x) = Complex.exp (refineLogCech X U V r hr l a x)) :
    LogCech.RationalCech.logarithmicSingularClass X V hV l' h' = LogCech.RationalCech.logarithmicSingularClass X U hU l h :=
  (LogCech.RationalCech.logarithmicSingularClass_log_independent X V hV l' (refineLogCech X U V r hr l)
    h' (exponentialCocycle_refinement X U V r hr l h) he).trans
    (logarithmicSingularClass_refinement X U V r hr hU hV l h)

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinement
