import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalizedRationalPencil
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.PositiveDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RationalParameterCharts

/-! # Pencil Fiber Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PencilFiberComparison

noncomputable section

/-! For a parameter with its two regular projective-line charts, the
normalized fiber construction is the original scheme's actual zero fiber.
All scalar fibers are therefore rationally equivalent even on a singular
proper parameter scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Z : Scheme} [IsIntegral Z]
  [AlgebraicGeometry.IsNoetherian Z] (f : Z ⟶ X.carrier) [IsProper f]

theorem fiber_eq (p : ℕ) (g : Z.functionField) (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
    let h := g - algebraMap ℂ Z.functionField a
    h ≠ 0 →
    (∀ x : Z,
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = h) ∨
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = h⁻¹)) →
    NormalizedRationalPencil.fiber X f p g a = NormalizedRationalPencil.Proper.fiber X f p g a := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
  intro h hh hreg
  let := Normalization.DivisorComparison.normalization_noetherian Z (f ≫ X.structureMap)
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Normalization.Scheme.normalizationMap Z ≫ (f ≫ X.structureMap))
  let φ := Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom (Normalization.Scheme.normalizationMap Z) (Normalization.Fields.normalizationMap_genericPoint Z) (f ≫ X.structureMap)
  have he : (Normalization.Fields.normalizationFieldIso Z).hom h =
      (Normalization.Fields.normalizationFieldIso Z).hom g - algebraMap ℂ (Normalization.Scheme.normalization Z).functionField a := by
    change φ (g - algebraMap ℂ Z.functionField a) = φ g - algebraMap ℂ (Normalization.Scheme.normalization Z).functionField a
    rw [map_sub, φ.commutes]
  change CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap Z ≫ f)
      (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization Z)
        ((Normalization.Fields.normalizationFieldIso Z).hom g - algebraMap ℂ (Normalization.Scheme.normalization Z).functionField a)))) =
    CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward f (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z h)))
  rw [← he, CyclePushforward.pointPushforward_comp, LinearMap.comp_apply,
    Normalization.PositiveDivisor.positiveDivisor Z (f ≫ X.structureMap) h hh hreg]

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) + p = m + 1)
    (g : Z.functionField)
    (hreg : ∀ x : Z,
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = g) ∨
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = g⁻¹)) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
    Transcendental ℂ g → ∀ a b : ℂ, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p
      (NormalizedRationalPencil.Proper.fiber X f p g a) (NormalizedRationalPencil.Proper.fiber X f p g b) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
  intro hg a b
  have hn (c : ℂ) : g - algebraMap ℂ Z.functionField c ≠ 0 := by
    intro he
    apply hg
    rw [sub_eq_zero.mp he]
    exact isAlgebraic_algebraMap c
  have hg0 : g ≠ 0 := by simpa only [map_zero, sub_zero] using hn 0
  have he := NormalizedRationalPencil.rationallyEquivalent X f m p hd g hg a b
  rw [fiber_eq X f p g a (hn a) (RationalParameterCharts.scalar_shift Z (f ≫ X.structureMap) g hg0 hreg a),
    fiber_eq X f p g b (hn b) (RationalParameterCharts.scalar_shift Z (f ≫ X.structureMap) g hg0 hreg b)] at he
  exact he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PencilFiberComparison
