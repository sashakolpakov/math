import OAI.AlgebraicGeometry.Cycles.Functoriality.UnitCap

/-! # Reduction -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.Reduction.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Linearity reduces compatibility for finite rational cycles to the
corresponding identity on each irreducible support. -/
theorem compatibility_iff_generators
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension) :
    (∀ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p,
      Y.geometricCycleClassMap q (UnitCap.cyclePushforward f hf p q hdeg z) =
        UnitCap.cohomologyPushforward f hf p q hdeg (X.geometricCycleClassMap p z)) ↔
    (∀ Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p,
      Y.geometricCycleClassMap q (UnitCap.cyclePushforwardGenerator f p q hdeg Z) =
        UnitCap.cohomologyPushforward f hf p q hdeg Z.geometricCycleClass) := by
  constructor
  · intro h Z
    have hz := h (Finsupp.single Z 1)
    simpa only [UnitCap.cyclePushforward_single,
      Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, one_smul] using hz
  · intro h
    have heq : (Y.geometricCycleClassMap q).comp (UnitCap.cyclePushforward f hf p q hdeg) =
        (UnitCap.cohomologyPushforward f hf p q hdeg).comp (X.geometricCycleClassMap p) := by
      apply Finsupp.lhom_ext
      intro Z a
      change Y.geometricCycleClassMap q
          (UnitCap.cyclePushforward f hf p q hdeg (Finsupp.single Z a)) =
        UnitCap.cohomologyPushforward f hf p q hdeg
          (X.geometricCycleClassMap p (Finsupp.single Z a))
      rw [UnitCap.cyclePushforward_single,
        Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, map_smul, map_smul, h Z]
    exact fun z => LinearMap.congr_fun heq z

/-- The source has no algebraic cycles in codimension above its dimension. -/
theorem compatibility_above_dimension
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hp : X.complexDimension < p) (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p) :
    Y.geometricCycleClassMap q (UnitCap.cyclePushforward f hf p q hdeg z) =
      UnitCap.cohomologyPushforward f hf p q hdeg (X.geometricCycleClassMap p z) := by
  have hz : z = 0 := CycleClass.Geometric.DimensionCycles.DimensionCycle.eq_zero_of_ambient_lt z (by
    rw [← X.complexDimension_eq_transcendenceDimension]
    exact hp)
  subst z
  simp only [map_zero]

/-- Applying target Poincare duality cancels its inverse in the
constructed cohomological pushforward. -/
theorem poincare_cohomologyPushforward
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hp : p ≤ X.complexDimension) (b : X.rationalCohomology (p + p)) :
    (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
        (UnitCap.targetComplementDegree p q hdeg hp)).hom
      (UnitCap.cohomologyPushforward f hf p q hdeg b) =
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (2 * (X.complexDimension - p))
      ((X.poincareDuality (p + p) (2 * (X.complexDimension - p))
        (UnitCap.sourceComplementDegree X p hp)).hom b) := by
  rw [UnitCap.cohomologyPushforward_eq_poincare f hf p q hdeg hp]
  exact (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
    (UnitCap.targetComplementDegree p q hdeg hp)).inv_hom_id_apply _

/-- In the valid degree range the desired equality is precisely equality
of the ordinary rational homology classes under the genuine pushforward. -/
theorem eq_pushforward_iff_poincare
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hp : p ≤ X.complexDimension)
    (a : Y.rationalCohomology (q + q)) (b : X.rationalCohomology (p + p)) :
    a = UnitCap.cohomologyPushforward f hf p q hdeg b ↔
    (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
        (UnitCap.targetComplementDegree p q hdeg hp)).hom a =
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (2 * (X.complexDimension - p))
      ((X.poincareDuality (p + p) (2 * (X.complexDimension - p))
        (UnitCap.sourceComplementDegree X p hp)).hom b) := by
  rw [← poincare_cohomologyPushforward f hf p q hdeg hp b]
  exact (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
    (UnitCap.targetComplementDegree p q hdeg hp)).toLinearEquiv.injective.eq_iff.symm

/-- The algebraic image in the dimension-preserving case has the usual
function-field multiplicity, already at the level of geometric classes. -/
theorem image_class_of_dimension_eq
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    Y.geometricCycleClassMap q (UnitCap.cyclePushforwardGenerator f p q hdeg Z) =
      (f.left.residueDegree Z.genericPoint : ℚ) •
        (show CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q from
          ⟨UnitCap.imageSupport f Z, UnitCap.imageCodimension_eq f p q hdeg Z hdim⟩).geometricCycleClass := by
  rw [UnitCap.cyclePushforwardGenerator_of_dimension_eq f p q hdeg Z hdim]
  exact Y.geometricCycleClassMap_single q
    ⟨UnitCap.imageSupport f Z, UnitCap.imageCodimension_eq f p q hdeg Z hdim⟩ _

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.Reduction.Construction
