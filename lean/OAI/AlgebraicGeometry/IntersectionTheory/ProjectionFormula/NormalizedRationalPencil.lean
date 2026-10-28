import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalParameter
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SchemePencilPoles

/-! # Normalized Rational Pencil -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalizedRationalPencil

noncomputable section

section

/-! Every finite scalar fiber of a rational pencil on a proper normal
parameter scheme gives the same native ambient Chow class. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Proper

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Z : Scheme} [IsIntegral Z]
  [AlgebraicGeometry.IsNoetherian Z] (f : Z ⟶ X.carrier) [IsProper f]

omit [IsProper f] in
def fiber (p : ℕ) (g : Z.functionField) (a : ℂ) : X.RationalDimensionCycle p :=
  letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
  CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward f
    (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z (g - algebraMap ℂ Z.functionField a))))

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) + p = m + 1)
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (g : Z.functionField) (hg : g ≠ 0) (a b : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
    g - algebraMap ℂ Z.functionField a ≠ 0 → g - algebraMap ℂ Z.functionField b ≠ 0 →
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (fiber X f p g a) (fiber X f p g b) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
  intro hga hgb
  have hpa := SchemePencilPoles.poles_sub_scalar Z (f ≫ X.structureMap) hNormal g hg a hga
  have hpb := SchemePencilPoles.poles_sub_scalar Z (f ≫ X.structureMap) hNormal g hg b hgb
  have ha := Proper.PrincipalParameter.zeros_poles X f m p hd (g - algebraMap ℂ Z.functionField a) hga
  have hb := Proper.PrincipalParameter.zeros_poles X f m p hd (g - algebraMap ℂ Z.functionField b) hgb
  rw [hpa] at ha
  rw [hpb] at hb
  exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X p ha (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X p hb)

theorem transcendental_fibers (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) + p = m + 1)
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (g : Z.functionField) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
    Transcendental ℂ g → ∀ a b : ℂ, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (fiber X f p g a) (fiber X f p g b) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
  intro hg a b
  have hn (c : ℂ) : g - algebraMap ℂ Z.functionField c ≠ 0 := by
    intro he
    apply hg
    rw [sub_eq_zero.mp he]
    exact (isAlgebraic_algebraMap c)
  have hg0 : g ≠ 0 := by simpa only [map_zero, sub_zero] using hn 0
  exact rationallyEquivalent X f m p hd hNormal g hg0 a b (hn a) (hn b)

end Proper

end

/-! Normalizing a proper integral parameter scheme constructs finite
pencil fibers with one ambient Chow class even for singular parameter schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Z : Scheme} [IsIntegral Z]
  [AlgebraicGeometry.IsNoetherian Z] (f : Z ⟶ X.carrier) [IsProper f]

def fiber (p : ℕ) (g : Z.functionField) (a : ℂ) : X.RationalDimensionCycle p :=
  letI := Normalization.DivisorComparison.normalization_noetherian Z (f ≫ X.structureMap)
  Proper.fiber X (Normalization.Scheme.normalizationMap Z ≫ f) p ((Normalization.Fields.normalizationFieldIso Z).hom g) a

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) + p = m + 1)
    (g : Z.functionField) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
    Transcendental ℂ g → ∀ a b : ℂ, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (fiber X f p g a) (fiber X f p g b) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ X.structureMap)
  intro hg a b
  let := Normalization.DivisorComparison.normalization_noetherian Z (f ≫ X.structureMap)
  let : IsFinite (Normalization.Scheme.normalizationMap Z) := Normalization.Scheme.normalizationMap_isFinite Z (f ≫ X.structureMap)
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.Scheme.normalizationMap Z) (Normalization.Fields.normalizationMap_genericPoint Z)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (Normalization.Fields.normalizationFieldMap_bijective Z)
  have hd' : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ((Normalization.Scheme.normalizationMap Z ≫ f) ≫ X.structureMap) + p = m + 1 := by
    rw [Category.assoc, ← BirationalPrincipalDivisor.dimension_eq_of_birational
      (Normalization.Scheme.normalizationMap Z) (Normalization.Fields.normalizationMap_genericPoint Z) (f ≫ X.structureMap)]
    exact hd
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Normalization.Scheme.normalizationMap Z ≫ (f ≫ X.structureMap))
  let e := AlgEquiv.ofBijective
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom (Normalization.Scheme.normalizationMap Z) (Normalization.Fields.normalizationMap_genericPoint Z) (f ≫ X.structureMap))
    (Normalization.Fields.normalizationFieldMap_bijective Z)
  have hg' : Transcendental ℂ (e g) := by
    intro h
    apply hg
    have hi := (h.isIntegral.map e.symm.toAlgHom).isAlgebraic
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using hi
  have h := Proper.transcendental_fibers X (Normalization.Scheme.normalizationMap Z ≫ f) m p hd'
    (Normalization.Scheme.normalization_stalk_integrallyClosed Z) ((Normalization.Fields.normalizationFieldIso Z).hom g)
  apply h _ a b
  change Transcendental ℂ (e g)
  exact hg'

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalizedRationalPencil
