import OAI.AlgebraicGeometry.Comparison.Betti.SplitCoordinateFlatness
import OAI.AlgebraicGeometry.Comparison.Betti.NoetherianHolomorphicGerms
import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialNe
import OAI.AlgebraicGeometry.Comparison.Betti.GermSliceDivision
import Mathlib.RingTheory.RingHom.Flat

/-! # Coordinate Flatness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoordinateFlatness.AnalyticLocal

noncomputable section

section

/-! The actual polynomial evaluation into holomorphic germs is flat over
the holomorphic parameter ring. -/

open _root_.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def centeredPolynomialGermMap (x : E) (c : ℂ) : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X] →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) :=
  eval₂RingHom (GermPolynomialNe.AnalyticLocal.parameterInclusion x c) (GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c)

theorem centeredCoordinateGerm_mem_maximalIdeal (x : E) (c : ℂ) :
    GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c ∈ IsLocalRing.maximalIdeal (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.isUnit_iff_value_ne_zero]
  change ¬(c - c ≠ 0)
  simp

theorem centeredPolynomialGermMap_flat [FiniteDimensional ℂ E] (x : E) (c : ℂ) :
    (centeredPolynomialGermMap x c).Flat := by
  let : Algebra (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X] (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) :=
    (centeredPolynomialGermMap x c).toAlgebra
  let : IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) := NoetherianHolomorphicGerms.AnalyticLocal.holomorphic_germ_noetherian x
  let : IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) := NoetherianHolomorphicGerms.AnalyticLocal.holomorphic_germ_noetherian (x, c)
  have h : Module.Flat (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X] (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) :=
    SplitCoordinateFlatness.AnalyticLocal.split_coordinate_flatness (GermPolynomialNe.AnalyticLocal.parameterInclusion x c) (GermPolynomialNe.AnalyticLocal.sliceEvaluation x c)
      (GermPolynomialNe.AnalyticLocal.sliceEvaluation_parameterInclusion x c) (GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c)
      (GermPolynomialNe.AnalyticLocal.sliceEvaluation_centeredCoordinate x c) (GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm_ne_zero x c)
      (centeredCoordinateGerm_mem_maximalIdeal x c) (GermSliceDivision.AnalyticLocal.germ_coordinate_division x c) rfl
  exact RingHom.flat_algebraMap_iff.mpr h

end

/-! Flatness of the original, uncentered polynomial evaluation map into
holomorphic germs follows by polynomial translation. -/

open _root_.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem centeredPolynomial_translation (x : E) (c : ℂ) :
    (centeredPolynomialGermMap x c).comp
      (algEquivAevalXAddC (GermMaps.AnalyticLocal.holomorphicConstantHom x c)).toRingEquiv.toRingHom =
      GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c := by
  apply Polynomial.ringHom_ext
  · intro a
    change centeredPolynomialGermMap x c
      (algEquivAevalXAddC (GermMaps.AnalyticLocal.holomorphicConstantHom x c) (C a)) =
        GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c (C a)
    rw [algEquivAevalXAddC_apply, aeval_C]
    change (C a).eval₂ (GermPolynomialNe.AnalyticLocal.parameterInclusion x c) (GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c) =
      (C a).eval₂ (GermPolynomialNe.AnalyticLocal.parameterInclusion x c) (GermPolynomialNe.AnalyticLocal.coordinateGerm x c)
    rw [eval₂_C, eval₂_C]
  · change centeredPolynomialGermMap x c
      (algEquivAevalXAddC (GermMaps.AnalyticLocal.holomorphicConstantHom x c) X) = GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c X
    rw [algEquivAevalXAddC_apply, aeval_X]
    change (X + C (GermMaps.AnalyticLocal.holomorphicConstantHom x c)).eval₂
      (GermPolynomialNe.AnalyticLocal.parameterInclusion x c) (GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c) =
        X.eval₂ (GermPolynomialNe.AnalyticLocal.parameterInclusion x c) (GermPolynomialNe.AnalyticLocal.coordinateGerm x c)
    rw [eval₂_add, eval₂_X, eval₂_C, eval₂_X]
    have hc : GermPolynomialNe.AnalyticLocal.parameterInclusion x c (GermMaps.AnalyticLocal.holomorphicConstantHom x c) = GermMaps.AnalyticLocal.holomorphicConstantHom (x, c) c := by
      apply Subtype.ext
      rfl
    rw [hc, GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm, sub_add_cancel]

theorem polynomialEvaluationGerm_flat [FiniteDimensional ℂ E] (x : E) (c : ℂ) :
    (GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c).Flat := by
  rw [← centeredPolynomial_translation]
  exact (RingHom.Flat.of_bijective (algEquivAevalXAddC (GermMaps.AnalyticLocal.holomorphicConstantHom x c)).bijective).comp
    (centeredPolynomialGermMap_flat x c)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoordinateFlatness.AnalyticLocal
