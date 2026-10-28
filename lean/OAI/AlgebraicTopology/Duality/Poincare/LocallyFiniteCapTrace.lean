import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapTruncation
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction
import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficientHomology
import OAI.AlgebraicTopology.Duality.Poincare.CapRelativeTrace

/-! # Locally Finite Cap Trace -/

namespace OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCapTrace

noncomputable section

/-!
# Compact relative traces of locally finite cap products

Actual finite truncation near a compact set identifies the relative quotient
of a locally finite cap product with the quotient of its ordinary finite cap.
The comparison uses the genuine relative chain projections.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The relative quotient of an actual locally finite cap can be computed
by the ordinary cap of the finite truncation of its input. -/
theorem locallyFiniteCap_scalarCompactRestriction {R : Type} [CommRing R]
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestrictionDegree R X K hK q
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap X p q c z) =
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection R X Kᶜ).f q
        (Products.Cap.singularCap X p q c
          (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactTruncation R X K hK (p + q) z)) := by
  apply AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestrictionDegree_eq_of_agrees
  intro τ hτ
  exact AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapTruncation.Cycles.locallyFiniteCap_truncation_agrees X K hK p q c z τ hτ

/-- For an integral locally finite input, the rational cap trace is the
ordinary mixed cap of its genuine finite integral truncation. -/
theorem locallyFiniteMixedCap_scalarCompactRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestrictionDegree ℚ X K hK q
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap X p q c (LocallyFiniteCoefficients.locallyFiniteIntegralToRational X (p + q) z)) =
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X Kᶜ).f q
        (IntegralCapCoefficients.mixedSingularCap X p q c (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X K hK (p + q) z)) := by
  apply AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestrictionDegree_eq_of_agrees
  intro τ hτ
  let a := AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X K hK (p + q) z
  have hnear : ∀ σ, (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X (p + q) σ ∩ K).Nonempty →
      LocallyFiniteCoefficients.locallyFiniteIntegralToRational X (p + q) z σ =
        AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℚ X (p + q)
          (IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X (p + q) a) σ := by
    intro σ hσ
    rw [← LocallyFiniteCoefficients.locallyFiniteIntegralToRational_ordinary]
    change (z σ : ℚ) = (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X (p + q) a σ : ℚ)
    dsimp only [a]
    rw [AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation_coefficients, ite_eq_left hσ]
  have h := AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapTruncation.Cycles.locallyFiniteCap_agrees_of_agrees X K p q c
    (LocallyFiniteCoefficients.locallyFiniteIntegralToRational X (p + q) z)
    (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℚ X (p + q)
      (IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X (p + q) a)) hnear τ hτ
  rw [AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap_ordinary] at h
  exact h

/-- The actual relative-empty cochain lift forgets to the given cochain. -/
theorem relativeEmptyCochainsIso_inv_inclusion (X : TopCat.{0}) (p : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p) :
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X ∅).f p
        ((CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv.f p c) = c :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom
      (CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv_hom_id p) c

/-- On representatives, the relative-empty cohomology lift is the actual
inverse cochain map applied to the cocycle. -/
theorem relativeEmptyCohomologyIso_inv_class (X : TopCat.{0}) (p : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X p) :
    (CapRelativeTrace.relativeEmptyCohomologyIso (ModuleCat.of ℚ ℚ) X p).inv
        (Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X p c) =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X ∅) p
        (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv p c) :=
  Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv p c

/-- The right relative quotient supplies the actual small-chain representative
of the ordinary action on relative homology. -/
theorem ordinaryRelativeCapHomology_small
    (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q)) :
    CapRelativeTrace.ordinaryRelativeCapHomology X B hB p q a z =
      SupportRelativeCapHomology.twoSupportSmallCapHomology X ∅ B p q
        ((CapRelativeTrace.relativeEmptyCohomologyIso (ModuleCat.of ℚ ℚ) X p).inv a)
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X ∅ B) (p + q) z) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyMap_comp (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X ∅ B)
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X ∅ B) (p + q)) z
  rw [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight_toRelative] at h
  rw [CapRelativeTrace.ordinaryRelativeCapHomology_apply, h]
  exact SupportRelativeCapHomology.twoSupportRelativeCapHomology_comparison X ∅ B isOpen_empty hB p q _ _

/-- A relative cycle need not lift to an absolute cycle. Its actual right
small-quotient image still gives the representative of ordinary relative cap. -/
theorem ordinaryRelativeCapHomology_class_class
    (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) (p + q)) :
    CapRelativeTrace.ordinaryRelativeCapHomology X B hB p q
        (Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X p c)
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q
        (SupportRelativeCapHomology.twoSupportSmallCapCycles X ∅ B p q
          (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv p c)
          (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X ∅ B) (p + q) z)) := by
  rw [ordinaryRelativeCapHomology_small, relativeEmptyCohomologyIso_inv_class,
    Cohomology.Singular.EvaluationNaturality.chainClass_naturality, SupportRelativeCapHomology.twoSupportSmallCapHomology_class_class]

/-- The empty-support small cap on an ambient chain is its ordinary mixed cap
followed by the genuine relative projection. -/
theorem twoSupportSmallCap_empty_projection
    (X : TopCat.{0}) (B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q)) :
    TwoSupportRelativeCap.twoSupportSmallCap X ∅ B p q
        ((CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv.f p c)
        ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X ∅ B).f (p + q)
          ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X B).f (p + q) z)) =
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q (IntegralCapCoefficients.mixedSingularCap X p q c z) := by
  have hz := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight_projection X ∅ B) (p + q)) z
  change (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X ∅ B).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X B).f (p + q) z) =
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X ∅ B).f (p + q) z at hz
  rw [hz, TwoSupportRelativeCap.twoSupportSmallCap_projection, relativeEmptyCochainsIso_inv_inclusion]

/-- The chain-level compact trace square for the actual mixed locally finite
cap, expressed in the existing small relative quotient. -/
theorem locallyFiniteMixedCap_compactRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestrictionDegree ℚ X K hK q
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles.locallyFiniteCap X p q c (LocallyFiniteCoefficients.locallyFiniteIntegralToRational X (p + q) z)) =
      TwoSupportRelativeCap.twoSupportSmallCap X ∅ Kᶜ p q
        ((CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv.f p c)
        ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X ∅ Kᶜ).f (p + q)
          (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestrictionDegree X K hK (p + q) z)) := by
  calc
    _ = (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X Kᶜ).f q
        (IntegralCapCoefficients.mixedSingularCap X p q c
          (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X K hK (p + q) z)) :=
      locallyFiniteMixedCap_scalarCompactRestriction X K hK p q c z
    _ = _ := (twoSupportSmallCap_empty_projection X Kᶜ p q c
      (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X K hK (p + q) z)).symm

/-- The exact relative quotient square restricts to the actual cycle modules. -/
theorem locallyFiniteMixedCapCycles_compactRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) (p + q)) :
    Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestriction ℚ X K hK) q
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapHomology.Cycles.locallyFiniteCapCycles X p q c
          (LocallyFiniteCoefficientHomology.locallyFiniteIntegralToRationalCycles X (p + q) z)) =
      SupportRelativeCapHomology.twoSupportSmallCapCycles X ∅ Kᶜ p q
        (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv p c)
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X ∅ Kᶜ) (p + q)
          (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X K hK) (p + q) z)) := by
  apply Subtype.ext
  exact locallyFiniteMixedCap_compactRestriction X K hK p q c.val z.val

/-- Cap followed by compact relative restriction is the ordinary relative cap
of the restricted integral locally finite class. Both sides use the original
native homology maps and the literal integer-to-rational coefficient change. -/
theorem locallyFiniteCapHomology_compactRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (hKc : IsOpen Kᶜ) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ X K hK q
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapHomology.Cycles.locallyFiniteCapHomology X p q a
          (LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology X (p + q) z)) =
      CapRelativeTrace.ordinaryRelativeCapHomology X Kᶜ hKc p q a
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X K hK (p + q) z) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X p a
  obtain ⟨w, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) (p + q) z
  rw [LocallyFiniteCoefficientHomology.locallyFiniteIntegralToRationalHomology_chainClass,
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapHomology.Cycles.locallyFiniteCapHomology_class_class, Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    Cohomology.Singular.EvaluationNaturality.chainClass_naturality, ordinaryRelativeCapHomology_class_class]
  exact congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X Kᶜ) q)
    (locallyFiniteMixedCapCycles_compactRestriction X K hK p q c w)

end

end OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCapTrace
