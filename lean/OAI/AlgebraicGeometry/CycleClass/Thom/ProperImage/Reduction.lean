import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass
import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! # Reduction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ProperImage.Reduction.Constructions

/-!
Canonical geometric operations for Functoriality. No cycle-class compatibility theorem
is assumed here. Residue fields at the generic points of reduced irreducible
supports are their function fields, so the native residue degree is the
function-field multiplicity in proper algebraic pushforward.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

/-- The irreducible closed support with generic point `f(η_Z)`. For a proper
morphism this is the image of the closed support `Z`. -/
def imageSupport {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) :
    IrreducibleCloseds Y.carrier :=
  irreducibleSetEquivPoints.symm (f.left Z.genericPoint)

theorem imageSupport_coe {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) :
    (imageSupport f Z : Set Y.carrier) = closure {f.left Z.genericPoint} := rfl

/-- Properness makes the closed support used by pushforward the actual
set-theoretic image, not just its closure. -/
theorem imageSupport_eq_image {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) :
    (imageSupport f Z : Set Y.carrier) = f.left '' (Z.1 : Set X.carrier) := by
  let φ : X.carrier ⟶ Y.carrier := f.left
  let : IsProper φ := hf
  have h := φ.isClosedMap.closure_image_eq_of_continuous
    φ.continuous {Z.genericPoint}
  change closure {φ Z.genericPoint} = φ '' (Z.1 : Set X.carrier)
  rw [Set.image_singleton, Z.genericPoint_spec] at h
  exact h

/-- Equality of source and image dimensions gives exactly the target
codimension prescribed by the cohomological degree shift. -/
theorem imageCodimension_eq {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    Geometric.DimensionCycles.dimensionCodimension Y (imageSupport f Z) = q := by
  have hs := Z.dimension_add_codimension
  have ht := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension Y (imageSupport f Z)
  rw [← X.complexDimension_eq_transcendenceDimension] at hs
  rw [← Y.complexDimension_eq_transcendenceDimension, hdim] at ht
  omega

/-- Proper pushforward on one irreducible support. It is zero if the image
dimension drops; otherwise its coefficient is `[κ(η_Z): κ(f(η_Z))]`. -/
def cyclePushforwardGenerator {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) : Geometric.DimensionCycles.RationalDimensionCycle Y q :=
  if hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap then
    Finsupp.single ⟨imageSupport f Z, imageCodimension_eq f p q hdeg Z hdim⟩
      (f.left.residueDegree Z.genericPoint : ℚ)
  else 0

/-- Algebraic proper pushforward, extended linearly from the usual
function-field-degree formula on irreducible supports. -/
def cyclePushforward {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension) :
    Geometric.DimensionCycles.RationalDimensionCycle X p →ₗ[ℚ] Geometric.DimensionCycles.RationalDimensionCycle Y q :=
  let _ : IsProper f.left := hf
  Finsupp.linearCombination ℚ (cyclePushforwardGenerator f p q hdeg)

theorem cyclePushforward_single {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) (a : ℚ) :
    cyclePushforward f hf p q hdeg (Finsupp.single Z a) =
      a • cyclePushforwardGenerator f p q hdeg Z :=
  Finsupp.linearCombination_single ℚ a Z

theorem cyclePushforwardGenerator_of_dimension_eq
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    cyclePushforwardGenerator f p q hdeg Z =
      Finsupp.single ⟨imageSupport f Z, imageCodimension_eq f p q hdeg Z hdim⟩
        (f.left.residueDegree Z.genericPoint : ℚ) := by
  simp only [cyclePushforwardGenerator, dite_eq_left hdim]

theorem cyclePushforwardGenerator_of_dimension_ne
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (imageSupport f Z) Y.structureMap ≠
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    cyclePushforwardGenerator f p q hdeg Z = 0 := by
  simp only [cyclePushforwardGenerator, dite_eq_right hdim]

/-- The complementary homological degree in the source. -/
theorem sourceComplementDegree (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (hp : p ≤ X.complexDimension) :
    (p + p) + 2 * (X.complexDimension - p) = 2 * X.complexDimension := by
  omega

/-- The same homological degree is complementary in the target. -/
theorem targetComplementDegree {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hp : p ≤ X.complexDimension) :
    (q + q) + 2 * (X.complexDimension - p) = 2 * Y.complexDimension := by
  omega

/-- Canonically oriented cohomological pushforward: cap with `[X]`, push
ordinary rational singular homology along the actual map of complex points,
and invert cap with `[Y]`. Above the source dimension the source cohomology
is zero, and the map is the zero linear map. -/
def cohomologyPushforward {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension) :
    X.rationalCohomology (p + p) →ₗ[ℚ]
      Y.rationalCohomology (q + q) :=
  let _ : IsProper f.left := hf
  if hp : p ≤ X.complexDimension then
    ((X.poincareDuality (p + p) (2 * (X.complexDimension - p))
        (sourceComplementDegree X p hp)).hom ≫
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
        (2 * (X.complexDimension - p)) ≫
      (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
        (targetComplementDegree p q hdeg hp)).inv).hom
  else 0

/-- On the possible degree range this is literally canonical cap,
ordinary homology pushforward, and inverse canonical cap. -/
theorem cohomologyPushforward_eq_poincare
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hp : p ≤ X.complexDimension) :
    cohomologyPushforward f hf p q hdeg =
      ((X.poincareDuality (p + p) (2 * (X.complexDimension - p))
          (sourceComplementDegree X p hp)).hom ≫
        AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
          (2 * (X.complexDimension - p)) ≫
        (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
          (targetComplementDegree p q hdeg hp)).inv).hom := by
  exact dite_eq_left hp

theorem cohomologyPushforward_of_dimension_lt
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hp : X.complexDimension < p) :
    cohomologyPushforward f hf p q hdeg = 0 := by
  simp [cohomologyPushforward, Nat.not_le_of_lt hp]

/-- The branch above the source dimension has a genuinely zero source. -/
theorem sourceCohomology_eq_zero (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (hp : X.complexDimension < p) (a : X.rationalCohomology (p + p)) :
    a = 0 := by
  let : Subsingleton (X.rationalCohomology (p + p)) :=
    ModuleCat.subsingleton_of_isZero
      (X.singularCohomology_isZero_above_dimension (p + p) (by omega))
  exact Subsingleton.elim a 0

/-- The actual constant-one singular cocycle, passed to degree-zero
cohomology. Its cocycle property and cup-unit laws are proved in the library. -/
def cohomologyUnit (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    X.rationalCohomology (0 + 0) :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver)

/-- The given map factors through the reduced support by a proper map
over `Spec ℂ` whose restriction to dense open subschemes is an isomorphism.
Smoothness and projectivity of the resolution source are bundled in `R`. -/
def Resolves {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (g : R.toOver ⟶ X.toOver) (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) : Prop :=
  ∃ π : R.carrier ⟶ Z.scheme,
    π ≫ Z.inclusion = g.left ∧
    π ≫ Z.structureMap = R.structureMap ∧
    IsProper π ∧
    ∃ e : R.carrier.PartialIso Z.scheme,
      e.source.ι ≫ π = e.iso.hom ≫ e.target.ι

end AlgebraicGeometry.CycleClass.Thom.ProperImage.Reduction.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.ProperImage.Reduction.Constructions.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-- Linearity reduces compatibility for finite rational cycles to the
corresponding identity on each irreducible support. -/
theorem compatibility_iff_generators
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension) :
    (∀ z : Geometric.DimensionCycles.RationalDimensionCycle X p,
      Y.geometricCycleClassMap q (cyclePushforward f hf p q hdeg z) =
        cohomologyPushforward f hf p q hdeg (X.geometricCycleClassMap p z)) ↔
    (∀ Z : Geometric.DimensionCycles.DimensionCycleSupport X p,
      Y.geometricCycleClassMap q (cyclePushforwardGenerator f p q hdeg Z) =
        cohomologyPushforward f hf p q hdeg Z.geometricCycleClass) := by
  constructor
  · intro h Z
    have hz := h (Finsupp.single Z 1)
    simpa only [cyclePushforward_single,
      Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, one_smul] using hz
  · intro h
    have heq : (Y.geometricCycleClassMap q).comp (cyclePushforward f hf p q hdeg) =
        (cohomologyPushforward f hf p q hdeg).comp (X.geometricCycleClassMap p) := by
      apply Finsupp.lhom_ext
      intro Z a
      change Y.geometricCycleClassMap q
          (cyclePushforward f hf p q hdeg (Finsupp.single Z a)) =
        cohomologyPushforward f hf p q hdeg
          (X.geometricCycleClassMap p (Finsupp.single Z a))
      rw [cyclePushforward_single,
        Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, map_smul, map_smul, h Z]
    exact fun z => LinearMap.congr_fun heq z

/-- The source has no algebraic cycles in codimension above its dimension. -/
theorem compatibility_above_dimension
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hp : X.complexDimension < p) (z : Geometric.DimensionCycles.RationalDimensionCycle X p) :
    Y.geometricCycleClassMap q (cyclePushforward f hf p q hdeg z) =
      cohomologyPushforward f hf p q hdeg (X.geometricCycleClassMap p z) := by
  have hz : z = 0 := Geometric.DimensionCycles.DimensionCycle.eq_zero_of_ambient_lt z (by
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
        (targetComplementDegree p q hdeg hp)).hom
      (cohomologyPushforward f hf p q hdeg b) =
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (2 * (X.complexDimension - p))
      ((X.poincareDuality (p + p) (2 * (X.complexDimension - p))
        (sourceComplementDegree X p hp)).hom b) := by
  rw [cohomologyPushforward_eq_poincare f hf p q hdeg hp]
  exact (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
    (targetComplementDegree p q hdeg hp)).inv_hom_id_apply _

/-- In the valid degree range the desired equality is precisely equality
of the ordinary rational homology classes under the genuine pushforward. -/
theorem eq_pushforward_iff_poincare
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hp : p ≤ X.complexDimension)
    (a : Y.rationalCohomology (q + q)) (b : X.rationalCohomology (p + p)) :
    a = cohomologyPushforward f hf p q hdeg b ↔
    (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
        (targetComplementDegree p q hdeg hp)).hom a =
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (2 * (X.complexDimension - p))
      ((X.poincareDuality (p + p) (2 * (X.complexDimension - p))
        (sourceComplementDegree X p hp)).hom b) := by
  rw [← poincare_cohomologyPushforward f hf p q hdeg hp b]
  exact (Y.poincareDuality (q + q) (2 * (X.complexDimension - p))
    (targetComplementDegree p q hdeg hp)).toLinearEquiv.injective.eq_iff.symm

/-- The algebraic image in the dimension-preserving case has the usual
function-field multiplicity, already at the level of geometric classes. -/
theorem image_class_of_dimension_eq
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    Y.geometricCycleClassMap q (cyclePushforwardGenerator f p q hdeg Z) =
      (f.left.residueDegree Z.genericPoint : ℚ) •
        (show Geometric.DimensionCycles.DimensionCycleSupport Y q from
          ⟨imageSupport f Z, imageCodimension_eq f p q hdeg Z hdim⟩).geometricCycleClass := by
  rw [cyclePushforwardGenerator_of_dimension_eq f p q hdeg Z hdim]
  exact Y.geometricCycleClassMap_single q
    ⟨imageSupport f Z, imageCodimension_eq f p q hdeg Z hdim⟩ _

end AlgebraicGeometry.CycleClass.Thom.ProperImage.Reduction.Constructions.Construction

end

end OAI
