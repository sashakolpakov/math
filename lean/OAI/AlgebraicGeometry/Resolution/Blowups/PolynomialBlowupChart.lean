import OAI.AlgebraicGeometry.Resolution.Blowups.ChartLift
import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialControlledTransform

/-! # Polynomial Blowup Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialBlowupChart.Construction

noncomputable section

/-! Actual Rees charts for a center `(I,z)` in a polynomial ring. -/

open _root_.Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- The coefficient `a`, viewed as a chosen element of the center `(I,z)`. -/
def polynomialCenterElement (I : Ideal R) (a : I) : Coefficient.Filtration.Construction.polynomialCenterIdeal I :=
  ⟨C a.val, (show I.map C ≤ Coefficient.Filtration.Construction.polynomialCenterIdeal I from le_sup_left)
    (Ideal.mem_map_of_mem C a.property)⟩

/-- The actual homogeneous-localization chart with denominator `a`. -/
abbrev polynomialBlowupChart (I : Ideal R) (a : I) :=
  Blowup.Charts.Construction.blowupChart (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a)

def polynomialBlowupBase (I : Ideal R) (a : I) : R[X] →+* polynomialBlowupChart I a :=
  Blowup.Charts.Construction.blowupChartConstants (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a)

def polynomialBlowupCoefficientBase (I : Ideal R) (a : I) : R →+* polynomialBlowupChart I a :=
  (polynomialBlowupBase I a).comp C

theorem polynomialBlowupCoefficientBase_center (I : Ideal R) (a : I) :
    I.map (polynomialBlowupCoefficientBase I a) =
      Ideal.span {polynomialBlowupCoefficientBase I a a.val} := by
  apply le_antisymm
  · change I.map ((polynomialBlowupBase I a).comp C) ≤ _
    rw [← Ideal.map_map]
    apply (Ideal.map_mono (show I.map C ≤ Coefficient.Filtration.Construction.polynomialCenterIdeal I from le_sup_left)).trans
    exact (ExceptionalIdeal.Construction.blowupChart_extendedIdeal (Coefficient.Filtration.Construction.polynomialCenterIdeal I)
      (polynomialCenterElement I a)).le
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ a.property

theorem polynomialBlowupCoefficientBase_regular (I : Ideal R) (a : I) :
    IsRegular (polynomialBlowupCoefficientBase I a a.val) :=
  ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a)

/-- The smaller coefficient blowup chart maps to the full chart. -/
def polynomialBlowupCoefficientMap (I : Ideal R) (a : I) :
    Blowup.Charts.Construction.blowupChart I a →+* polynomialBlowupChart I a :=
  ChartLift.Construction.blowupChartLift I a (polynomialBlowupCoefficientBase I a)
    (polynomialBlowupCoefficientBase_center I a) (polynomialBlowupCoefficientBase_regular I a)

theorem polynomialBlowupCoefficientMap_constants (I : Ideal R) (a : I) (r : R) :
    polynomialBlowupCoefficientMap I a (Blowup.Charts.Construction.blowupChartConstants I a r) =
      polynomialBlowupBase I a (C r) :=
  ChartLift.Construction.blowupChartLift_constants I a (polynomialBlowupCoefficientBase I a)
    (polynomialBlowupCoefficientBase_center I a) (polynomialBlowupCoefficientBase_regular I a) r

/-- The new distinguished coordinate is the actual homogeneous fraction `z/a`. -/
def polynomialBlowupNewVariable (I : Ideal R) (a : I) : polynomialBlowupChart I a :=
  ExceptionalIdeal.Construction.blowupChartRatio (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a)
    ⟨X, (show Ideal.span {X} ≤ Coefficient.Filtration.Construction.polynomialCenterIdeal I from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton X))⟩

theorem polynomialBlowupNewVariable_relation (I : Ideal R) (a : I) :
    polynomialBlowupBase I a (C a.val) * polynomialBlowupNewVariable I a =
      polynomialBlowupBase I a X :=
  ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a) _

/-- Polynomial evaluation gives one direction of the chart identification. -/
def polynomialBlowupFromPolynomial (I : Ideal R) (a : I) :
    (Blowup.Charts.Construction.blowupChart I a)[X] →+* polynomialBlowupChart I a :=
  eval₂RingHom (polynomialBlowupCoefficientMap I a) (polynomialBlowupNewVariable I a)

theorem scaledPolynomialMap_center_eq (I : Ideal R) (a : I) :
    (Coefficient.Filtration.Construction.polynomialCenterIdeal I).map
        (PolynomialControlledTransform.Construction.scaledPolynomialMap (Blowup.Charts.Construction.blowupChartConstants I a) (Blowup.Charts.Construction.blowupChartConstants I a a.val)) =
      Ideal.span {C (Blowup.Charts.Construction.blowupChartConstants I a a.val)} := by
  apply le_antisymm
  · exact PolynomialControlledTransform.Construction.scaledPolynomialMap_center_le I _ _ (ExceptionalIdeal.Construction.blowupChart_extendedIdeal I a).le
  · rw [Ideal.span_singleton_le_iff_mem]
    have h := Ideal.mem_map_of_mem
      (PolynomialControlledTransform.Construction.scaledPolynomialMap (Blowup.Charts.Construction.blowupChartConstants I a) (Blowup.Charts.Construction.blowupChartConstants I a a.val))
      (polynomialCenterElement I a).property
    simpa only [polynomialCenterElement, PolynomialControlledTransform.Construction.scaledPolynomialMap_apply, map_C, C_comp] using h

/-- The chart universal property supplies the reverse map to the polynomial ring. -/
def polynomialBlowupToPolynomial (I : Ideal R) (a : I) :
    polynomialBlowupChart I a →+* (Blowup.Charts.Construction.blowupChart I a)[X] :=
  ChartLift.Construction.blowupChartLift (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a)
    (PolynomialControlledTransform.Construction.scaledPolynomialMap (Blowup.Charts.Construction.blowupChartConstants I a) (Blowup.Charts.Construction.blowupChartConstants I a a.val))
    (by
      simpa only [polynomialCenterElement, PolynomialControlledTransform.Construction.scaledPolynomialMap_apply, map_C, C_comp]
        using scaledPolynomialMap_center_eq I a)
    (by
      simpa only [polynomialCenterElement, PolynomialControlledTransform.Construction.scaledPolynomialMap_apply, map_C, C_comp]
        using PolynomialControlledTransform.Construction.polynomial_C_regular (Blowup.Charts.Construction.blowupChartConstants I a a.val)
          (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a))

theorem polynomialBlowupToPolynomial_base (I : Ideal R) (a : I) (p : R[X]) :
    polynomialBlowupToPolynomial I a (polynomialBlowupBase I a p) =
      PolynomialControlledTransform.Construction.scaledPolynomialMap (Blowup.Charts.Construction.blowupChartConstants I a) (Blowup.Charts.Construction.blowupChartConstants I a a.val) p :=
  ChartLift.Construction.blowupChartLift_constants (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a) _ _ _ p

theorem polynomialBlowupFromPolynomial_C (I : Ideal R) (a : I) (r : Blowup.Charts.Construction.blowupChart I a) :
    polynomialBlowupFromPolynomial I a (C r) = polynomialBlowupCoefficientMap I a r :=
  eval₂_C _ _

theorem polynomialBlowupFromPolynomial_X (I : Ideal R) (a : I) :
    polynomialBlowupFromPolynomial I a X = polynomialBlowupNewVariable I a :=
  eval₂_X _ _

/-- Composing the coordinate substitution with evaluation on the actual
chart recovers its original base map. -/
theorem polynomialBlowupFromPolynomial_scaled (I : Ideal R) (a : I) :
    (polynomialBlowupFromPolynomial I a).comp
        (PolynomialControlledTransform.Construction.scaledPolynomialMap (Blowup.Charts.Construction.blowupChartConstants I a) (Blowup.Charts.Construction.blowupChartConstants I a a.val)) =
      polynomialBlowupBase I a := by
  apply Polynomial.ringHom_ext
  · intro r
    change polynomialBlowupFromPolynomial I a
      (PolynomialControlledTransform.Construction.scaledPolynomialMap (Blowup.Charts.Construction.blowupChartConstants I a) (Blowup.Charts.Construction.blowupChartConstants I a a.val) (C r)) = _
    rw [PolynomialControlledTransform.Construction.scaledPolynomialMap_apply, map_C, C_comp, polynomialBlowupFromPolynomial_C,
      polynomialBlowupCoefficientMap_constants]
  · change polynomialBlowupFromPolynomial I a
      (PolynomialControlledTransform.Construction.scaledPolynomialMap (Blowup.Charts.Construction.blowupChartConstants I a) (Blowup.Charts.Construction.blowupChartConstants I a a.val) X) = _
    rw [PolynomialControlledTransform.Construction.scaledPolynomialMap_apply, map_X, X_comp, map_mul,
      polynomialBlowupFromPolynomial_C, polynomialBlowupFromPolynomial_X,
      polynomialBlowupCoefficientMap_constants, polynomialBlowupNewVariable_relation]

theorem polynomialBlowupToPolynomial_coefficientMap (I : Ideal R) (a : I) :
    (polynomialBlowupToPolynomial I a).comp (polynomialBlowupCoefficientMap I a) =
      (C : Blowup.Charts.Construction.blowupChart I a →+* (Blowup.Charts.Construction.blowupChart I a)[X]) := by
  apply ChartLift.Construction.blowupChart_hom_ext I a (C.comp (Blowup.Charts.Construction.blowupChartConstants I a))
    (PolynomialControlledTransform.Construction.polynomial_C_regular _ (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a))
  · intro r
    change polynomialBlowupToPolynomial I a
      (polynomialBlowupCoefficientMap I a (Blowup.Charts.Construction.blowupChartConstants I a r)) = _
    rw [polynomialBlowupCoefficientMap_constants, polynomialBlowupToPolynomial_base,
      PolynomialControlledTransform.Construction.scaledPolynomialMap_apply, map_C, C_comp]
    rfl
  · intro r
    rfl

theorem polynomialBlowupToPolynomial_newVariable (I : Ideal R) (a : I) :
    polynomialBlowupToPolynomial I a (polynomialBlowupNewVariable I a) = X := by
  apply (PolynomialControlledTransform.Construction.polynomial_C_regular _ (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)).left
  have h := congrArg (polynomialBlowupToPolynomial I a)
    (polynomialBlowupNewVariable_relation I a)
  simpa only [map_mul, polynomialBlowupToPolynomial_base, PolynomialControlledTransform.Construction.scaledPolynomialMap_apply,
    map_C, C_comp, map_X, X_comp] using h

theorem polynomialBlowupFromPolynomial_toPolynomial (I : Ideal R) (a : I) :
    (polynomialBlowupFromPolynomial I a).comp (polynomialBlowupToPolynomial I a) =
      RingHom.id (polynomialBlowupChart I a) := by
  apply ChartLift.Construction.blowupChart_hom_ext (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a)
    (polynomialBlowupBase I a)
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular (Coefficient.Filtration.Construction.polynomialCenterIdeal I) (polynomialCenterElement I a))
  · intro p
    change polynomialBlowupFromPolynomial I a
      (polynomialBlowupToPolynomial I a (polynomialBlowupBase I a p)) = _
    rw [polynomialBlowupToPolynomial_base]
    exact congrArg (fun f : R[X] →+* polynomialBlowupChart I a => f p)
      (polynomialBlowupFromPolynomial_scaled I a)
  · intro p
    rfl

theorem polynomialBlowupToPolynomial_fromPolynomial (I : Ideal R) (a : I) :
    (polynomialBlowupToPolynomial I a).comp (polynomialBlowupFromPolynomial I a) =
      RingHom.id ((Blowup.Charts.Construction.blowupChart I a)[X]) := by
  apply Polynomial.ringHom_ext
  · intro r
    change polynomialBlowupToPolynomial I a
      (polynomialBlowupFromPolynomial I a (C r)) = C r
    rw [polynomialBlowupFromPolynomial_C]
    exact congrArg (fun f : Blowup.Charts.Construction.blowupChart I a →+* (Blowup.Charts.Construction.blowupChart I a)[X] => f r)
      (polynomialBlowupToPolynomial_coefficientMap I a)
  · change polynomialBlowupToPolynomial I a (polynomialBlowupFromPolynomial I a X) = X
    rw [polynomialBlowupFromPolynomial_X, polynomialBlowupToPolynomial_newVariable]

/-- The actual Rees chart for `(I,z)` with denominator `a` is the polynomial
ring over `R[I/a]`, with new variable `z/a`. -/
def polynomialBlowupChartEquiv (I : Ideal R) (a : I) :
    polynomialBlowupChart I a ≃+* (Blowup.Charts.Construction.blowupChart I a)[X] :=
  RingEquiv.ofRingHom (polynomialBlowupToPolynomial I a) (polynomialBlowupFromPolynomial I a)
    (polynomialBlowupToPolynomial_fromPolynomial I a)
    (polynomialBlowupFromPolynomial_toPolynomial I a)

theorem polynomialBlowupChartEquiv_base (I : Ideal R) (a : I) (p : R[X]) :
    polynomialBlowupChartEquiv I a (polynomialBlowupBase I a p) =
      (p.map (Blowup.Charts.Construction.blowupChartConstants I a)).comp (C (Blowup.Charts.Construction.blowupChartConstants I a a.val) * X) :=
  polynomialBlowupToPolynomial_base I a p

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialBlowupChart.Construction
