import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass
import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Birational.Birational
import OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology

/-! # Unit Cap -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Cycles.Functoriality.UnitCap

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
    (f : X.toOver ⟶ Y.toOver) {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    IrreducibleCloseds Y.carrier :=
  irreducibleSetEquivPoints.symm (f.left Z.genericPoint)

theorem imageSupport_coe {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    (imageSupport f Z : Set Y.carrier) = closure {f.left Z.genericPoint} := rfl

/-- Properness makes the closed support used by pushforward the actual
set-theoretic image, not just its closure. -/
theorem imageSupport_eq_image {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
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
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    CycleClass.Geometric.DimensionCycles.dimensionCodimension Y (imageSupport f Z) = q := by
  have hs := Z.dimension_add_codimension
  have ht := CycleClass.Geometric.DimensionCycles.supportDimension_add_dimensionCodimension Y (imageSupport f Z)
  rw [← X.complexDimension_eq_transcendenceDimension] at hs
  rw [← Y.complexDimension_eq_transcendenceDimension, hdim] at ht
  omega

/-- Proper pushforward on one irreducible support. It is zero if the image
dimension drops; otherwise its coefficient is `[κ(η_Z): κ(f(η_Z))]`. -/
def cyclePushforwardGenerator {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle Y q :=
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
    CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p →ₗ[ℚ] CycleClass.Geometric.DimensionCycles.RationalDimensionCycle Y q :=
  let _ : IsProper f.left := hf
  Finsupp.linearCombination ℚ (cyclePushforwardGenerator f p q hdeg)

theorem cyclePushforward_single {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (a : ℚ) :
    cyclePushforward f hf p q hdeg (Finsupp.single Z a) =
      a • cyclePushforwardGenerator f p q hdeg Z :=
  Finsupp.linearCombination_single ℚ a Z

theorem cyclePushforwardGenerator_of_dimension_eq
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
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
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
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
    (g : R.toOver ⟶ X.toOver) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) : Prop :=
  ∃ π : R.carrier ⟶ Z.scheme,
    π ≫ Z.inclusion = g.left ∧
    π ≫ Z.structureMap = R.structureMap ∧
    IsProper π ∧
    ∃ e : R.carrier.PartialIso Z.scheme,
      e.source.ι ≫ π = e.iso.hom ≫ e.target.ι

end AlgebraicGeometry.Cycles.Functoriality.UnitCap

namespace AlgebraicGeometry.Cycles.Functoriality.UnitCap.Construction

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

/-- The constant-one cochain caps a simplex to that same simplex. -/
theorem cap_cupUnit_chain (K : SSet.{0}) (n : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℚ) K).X n) :
    AlgebraicTopology.Products.Cap.cap K 0 n (AlgebraicTopology.Products.Cup.cupUnit K) (AlgebraicTopology.Products.Cap.chainCast K (Nat.zero_add n).symm z) = z := by
  have h : (AlgebraicTopology.Products.Cap.cap K 0 n (AlgebraicTopology.Products.Cup.cupUnit (R := ℚ) K)).comp (AlgebraicTopology.Products.Cap.chainCast K (Nat.zero_add n).symm) =
      LinearMap.id := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext K ((AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℚ) K).X n)
    intro s
    simp only [LinearMap.comp_apply, AlgebraicTopology.Products.Cap.chainCast_simplex, AlgebraicTopology.Products.Cap.cap_simplex,
      AlgebraicTopology.Products.Cup.backFace_zero_left, LinearMap.id_apply]
    exact (congrArg (fun a : ℚ => a • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) K s)
      (AlgebraicTopology.Products.Cup.evaluation_cupUnit (R := ℚ) K
        (AlgebraicTopology.Products.SimplexFaceIdentities.frontFace K 0 n (AlgebraicTopology.Products.SimplexFaceIdentities.simplexCast K (Nat.zero_add n).symm s)))).trans (one_smul ℚ _)
  exact LinearMap.congr_fun h z

def chainCycleDegreeCast {R : Type} [CommRing R] (C : ChainComplex (ModuleCat.{0} R) ℕ)
    {i j : ℕ} (h : i = j) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C i) : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C j := h ▸ z

theorem chainCycleDegreeCast_val {R : Type} [CommRing R] (C : ChainComplex (ModuleCat.{0} R) ℕ)
    {i j : ℕ} (h : i = j) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C i) :
    (chainCycleDegreeCast C h z).val = (eqToHom (congrArg C.X h)) z.val := by
  subst j
  rfl

theorem chainClass_degreeCast {R : Type} [CommRing R] (C : ChainComplex (ModuleCat.{0} R) ℕ)
    {i j : ℕ} (h : i = j) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C i) :
    (eqToHom (congrArg (fun k => C.homology k) h)) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C i z) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C j (chainCycleDegreeCast C h z) := by
  subst j
  rfl

/-- Capping with the actual degree-zero unit acts as the identity on
rational homology, with its degree transport displayed explicitly. -/
theorem cap_cohomologyCupUnit (K : SSet.{0}) (n : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℚ) K).homology n) :
    AlgebraicTopology.Products.CapBoundary.capHomology K 0 n (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit K)
      ((eqToHom (congrArg (fun k => (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℚ) K).homology k)
        (Nat.zero_add n).symm)) z) = z := by
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℚ) K) n z
  rw [chainClass_degreeCast]
  change AlgebraicTopology.Products.CapBoundary.capHomology K 0 n
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℚ ℚ)) 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit K))
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (0 + n) (chainCycleDegreeCast _ (Nat.zero_add n).symm z)) = _
  rw [AlgebraicTopology.Products.CapBoundary.capHomology_class_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℚ) K) n)
  apply Subtype.ext
  change AlgebraicTopology.Products.Cap.cap K 0 n (AlgebraicTopology.Products.Cup.cupUnit K) (chainCycleDegreeCast _ (Nat.zero_add n).symm z).val = z.val
  rw [chainCycleDegreeCast_val]
  exact cap_cupUnit_chain K n z.val

/-- Coefficient change commutes with equality of homological degrees. -/
theorem integralToScalarSingularHomology_degreeCast (X : TopCat.{0})
    {i j : ℕ} (h : i = j) (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology i) :
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X j
      ((eqToHom (congrArg (fun k => (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology k) h)) z) =
    (eqToHom (congrArg (fun k => (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology k) h))
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X i z) := by
  subst j
  rfl

/-- The mixed integral/rational cap with the unit is actual coefficient change. -/
theorem mixedSingularCapHomology_unit (X : TopCat.{0}) (n : ℕ)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) :
    AlgebraicTopology.Duality.Poincare.MixedCapHomology.mixedSingularCapHomology X 0 n (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℚ) X)
      ((eqToHom (congrArg (fun k => (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology k)
        (Nat.zero_add n).symm)) z) = AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X n z := by
  rw [AlgebraicTopology.Duality.Poincare.MixedCapHomology.mixedSingularCapHomology_apply]
  exact (congrArg (AlgebraicTopology.Products.CapBoundary.singularCapHomology X 0 n (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℚ) X))
    (integralToScalarSingularHomology_degreeCast X (Nat.zero_add n).symm z)).trans
    (cap_cohomologyCupUnit (TopCat.toSSet.obj X) n _)

end AlgebraicGeometry.Cycles.Functoriality.UnitCap.Construction

end

end OAI
