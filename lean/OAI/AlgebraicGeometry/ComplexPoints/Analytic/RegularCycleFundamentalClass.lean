import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocallyFiniteFundamental
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap
import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients

/-! # Regular Cycle Fundamental Class -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularCycleFundamentalClass

noncomputable section

/-!
# Genuine locally finite classes of a cycle's regular locus

The analytic spaces are the native complex points of the variety and of the
actual algebraic regular locus. Their proved complex manifold structures
provide canonical locally finite fundamental classes. Removing the singular
boundary makes the regular-locus inclusion a closed embedding, hence proper;
its genuine locally finite pushforward is therefore defined.

This file constructs that pushforward class. It does not identify it with a
cap product or assert localization at a singular support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem lfProperHomology_degree_transport (R : Type) [Ring R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsProperMap f) {i j : ℕ} (h : i = j)
    (a : (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology i) :
    CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf j
        ((eqToHom (congrArg (fun n => (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n) h)) a) =
      (eqToHom (congrArg (fun n => (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R Y).homology n) h))
        (CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R f hf i a) := by
  subst j
  rfl

private theorem lfRationalHomology_degree_transport (X : TopCat.{0})
    {i j : ℕ} (h : i = j) (a : (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology i) :
    AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology X j
        ((eqToHom (congrArg (fun n => (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n) h)) a) =
      (eqToHom (congrArg (fun n => (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X).homology n) h))
        (AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology X i a) := by
  subst j
  rfl

namespace IntegralProjectiveVariety

/-- The canonical integral locally finite class of the genuine analytic
manifold of a smooth integral projective variety. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticLocallyFiniteFundamentalClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of V.analyticSpace)).homology
      (2 * V.complexDimension) :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass V.complexDimension V.analyticSpace

/-- Its point restriction is the actual canonical complex local generator. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticLocallyFiniteFundamentalClass_atPoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : V.analyticSpace) :
    CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of V.analyticSpace) x
        (2 * V.complexDimension) V.analyticLocallyFiniteFundamentalClass =
      CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := V.complexDimension) x :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_atPoint V.complexDimension V.analyticSpace x

/-- The genuine compact comparison identifies this class with the ordinary
canonical fundamental class of the projective analytic manifold. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticLocallyFiniteFundamentalClass_compactComparison
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (CycleClass.Geometric.LocallyFiniteComparison.Cycles.locallyFiniteOrdinaryHomologyIso ℤ (TopCat.of V.analyticSpace)
        (2 * V.complexDimension)).hom V.analyticLocallyFiniteFundamentalClass =
      CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass V.complexDimension V.analyticSpace :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_compactComparison V.complexDimension V.analyticSpace

theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticLocallyFiniteFundamentalClass_ne_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.analyticLocallyFiniteFundamentalClass ≠ 0 :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_ne_zero V.complexDimension V.analyticSpace

/-- The rational fundamental class is the image of the canonical integral
class under the actual coefficient-change map on locally finite homology. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticRationalLocallyFiniteFundamentalClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ (TopCat.of V.analyticSpace)).homology
      (2 * V.complexDimension) :=
  AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of V.analyticSpace)
    (2 * V.complexDimension) V.analyticLocallyFiniteFundamentalClass

end IntegralProjectiveVariety

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The canonical integral locally finite class of the actual nonempty
regular locus, in its derived manifold dimension. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocallyFiniteFundamentalClass (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of Z.regularAnalyticSpace)).homology
      (2 * Z.regularComplexDimension) :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass Z.regularComplexDimension Z.regularAnalyticSpace

/-- Every point has its proved canonical complex local value. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocallyFiniteFundamentalClass_atPoint (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of Z.regularAnalyticSpace) x
        (2 * Z.regularComplexDimension) Z.regularLocallyFiniteFundamentalClass =
      CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := Z.regularComplexDimension) x :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_atPoint
    Z.regularComplexDimension Z.regularAnalyticSpace x

/-- Restriction to every actual compact subset gives its canonical compact
fundamental class, independently of a chosen exhaustion. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocallyFiniteFundamentalClass_restriction (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (K : Set Z.regularAnalyticSpace) (hK : IsCompact K) :
    CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction (TopCat.of Z.regularAnalyticSpace) K hK
        (2 * Z.regularComplexDimension) Z.regularLocallyFiniteFundamentalClass =
      CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension K hK :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_restriction
    Z.regularComplexDimension Z.regularAnalyticSpace K hK

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocallyFiniteFundamentalClass_ne_zero (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularLocallyFiniteFundamentalClass ≠ 0 :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_ne_zero
    Z.regularComplexDimension Z.regularAnalyticSpace

/-- The locally finite fundamental degree agrees with the cycle codimension,
by the proved dimension of the actual regular locus. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularFundamentalDegree_eq (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    2 * Z.regularComplexDimension = 2 * (V.complexDimension - p) :=
  congrArg (fun n : ℕ => 2 * n) Z.regularComplexDimension_eq_sub

/-- Only the degree is transported: the class is the canonical class of
the same actual regular-locus manifold. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocallyFiniteFundamentalClassInCodimension (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of Z.regularAnalyticSpace)).homology
      (2 * (V.complexDimension - p)) :=
  (eqToHom (congrArg
    (fun n => (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of Z.regularAnalyticSpace)).homology n)
    Z.regularFundamentalDegree_eq)) Z.regularLocallyFiniteFundamentalClass

/-- The ambient boundary complement has its own canonical locally finite
class, with its inherited complex manifold structure and ambient dimension. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientLocallyFiniteFundamentalClass (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of Z.regularAmbientSpace)).homology
      (2 * V.complexDimension) :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass V.complexDimension Z.regularAmbientSpace

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientLocallyFiniteFundamentalClass_atPoint (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAmbientSpace) :
    CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction (TopCat.of Z.regularAmbientSpace) x
        (2 * V.complexDimension) Z.regularAmbientLocallyFiniteFundamentalClass =
      CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := V.complexDimension) x :=
  CycleClass.Geometric.ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_atPoint V.complexDimension Z.regularAmbientSpace x

/-- The regular locus maps to the boundary complement by the already proved
continuous codomain restriction of its native algebraic point map. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementTopCatMap (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    TopCat.of Z.regularAnalyticSpace ⟶ TopCat.of Z.regularAmbientSpace :=
  TopCat.ofHom ⟨Z.regularComplementInclusion, Z.continuous_regularComplementInclusion⟩

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementTopCatMap_apply (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Z.regularComplementTopCatMap x = Z.regularComplementInclusion x := rfl

/-- Closedness of the actual embedded regular locus in this complement
proves properness; no compactness of the regular locus is assumed. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.isProperMap_regularComplementInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    IsProperMap Z.regularComplementInclusion :=
  Z.isClosedEmbedding_regularComplementInclusion.isProperMap

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.isProperMap_regularComplementTopCatMap (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    IsProperMap Z.regularComplementTopCatMap :=
  Z.isProperMap_regularComplementInclusion

/-- The genuine locally finite homology pushforward along the actual
proper regular-locus inclusion, with arbitrary ring coefficients. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocallyFinitePushforward (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (R : Type) [Ring R] (n : ℕ) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R (TopCat.of Z.regularAnalyticSpace)).homology n ⟶
      (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R (TopCat.of Z.regularAmbientSpace)).homology n :=
  CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap R Z.regularComplementTopCatMap
    Z.isProperMap_regularComplementTopCatMap n

/-- The integral locally finite cycle class in the complement of the
singular boundary, obtained by actual proper pushforward of the regular
fundamental class in the proved codimension degree. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCycleLocallyFiniteClass (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of Z.regularAmbientSpace)).homology
      (2 * (V.complexDimension - p)) :=
  Z.regularLocallyFinitePushforward ℤ (2 * (V.complexDimension - p))
    Z.regularLocallyFiniteFundamentalClassInCodimension

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCycleLocallyFiniteClass_eq_pushforward (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularCycleLocallyFiniteClass =
      CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ Z.regularComplementTopCatMap
        Z.isProperMap_regularComplementTopCatMap (2 * (V.complexDimension - p))
        Z.regularLocallyFiniteFundamentalClassInCodimension := rfl

/-- Proper pushforward commutes with the proved degree identification, so
the same class is obtained by pushing in the native dimension first. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCycleLocallyFiniteClass_eq_transport_pushforward
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularCycleLocallyFiniteClass =
      (eqToHom (congrArg
        (fun n => (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ (TopCat.of Z.regularAmbientSpace)).homology n)
        Z.regularFundamentalDegree_eq))
        (Z.regularLocallyFinitePushforward ℤ (2 * Z.regularComplexDimension)
          Z.regularLocallyFiniteFundamentalClass) :=
  lfProperHomology_degree_transport ℤ Z.regularComplementTopCatMap
    Z.isProperMap_regularComplementTopCatMap Z.regularFundamentalDegree_eq
    Z.regularLocallyFiniteFundamentalClass

/-- The actual rational coefficient image of the regular-locus fundamental class. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalLocallyFiniteFundamentalClass (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ (TopCat.of Z.regularAnalyticSpace)).homology
      (2 * Z.regularComplexDimension) :=
  AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of Z.regularAnalyticSpace)
    (2 * Z.regularComplexDimension) Z.regularLocallyFiniteFundamentalClass

/-- Rational coefficients and the actual codimension degree, on the same
regular-locus locally finite homology class. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalLocallyFiniteFundamentalClassInCodimension
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ (TopCat.of Z.regularAnalyticSpace)).homology
      (2 * (V.complexDimension - p)) :=
  AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of Z.regularAnalyticSpace)
    (2 * (V.complexDimension - p)) Z.regularLocallyFiniteFundamentalClassInCodimension

/-- Coefficient change and reindexing by the proved dimension equality agree. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalLocallyFiniteFundamentalClassInCodimension_eq_transport
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularRationalLocallyFiniteFundamentalClassInCodimension =
      (eqToHom (congrArg
        (fun n => (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ (TopCat.of Z.regularAnalyticSpace)).homology n)
        Z.regularFundamentalDegree_eq)) Z.regularRationalLocallyFiniteFundamentalClass :=
  lfRationalHomology_degree_transport (TopCat.of Z.regularAnalyticSpace)
    Z.regularFundamentalDegree_eq Z.regularLocallyFiniteFundamentalClass

/-- The actual rational fundamental class of the ambient boundary complement. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientRationalLocallyFiniteFundamentalClass (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ (TopCat.of Z.regularAmbientSpace)).homology
      (2 * V.complexDimension) :=
  AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of Z.regularAmbientSpace)
    (2 * V.complexDimension) Z.regularAmbientLocallyFiniteFundamentalClass

/-- The genuine rational proper pushforward of the regular fundamental class. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalCycleLocallyFiniteClass (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ (TopCat.of Z.regularAmbientSpace)).homology
      (2 * (V.complexDimension - p)) :=
  Z.regularLocallyFinitePushforward ℚ (2 * (V.complexDimension - p))
    Z.regularRationalLocallyFiniteFundamentalClassInCodimension

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalCycleLocallyFiniteClass_eq_pushforward (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularRationalCycleLocallyFiniteClass =
      CycleClass.Geometric.LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℚ Z.regularComplementTopCatMap
        Z.isProperMap_regularComplementTopCatMap (2 * (V.complexDimension - p))
        Z.regularRationalLocallyFiniteFundamentalClassInCodimension := rfl

/-- The rational cycle class is exactly the coefficient image of the
integral pushed class, by actual proper-pushforward naturality. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularRationalCycleLocallyFiniteClass_eq_rationalize (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularRationalCycleLocallyFiniteClass =
      AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology (TopCat.of Z.regularAmbientSpace)
        (2 * (V.complexDimension - p)) Z.regularCycleLocallyFiniteClass :=
  AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology_naturality Z.regularComplementTopCatMap
    Z.isProperMap_regularComplementTopCatMap (2 * (V.complexDimension - p))
    Z.regularLocallyFiniteFundamentalClassInCodimension

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularCycleFundamentalClass
