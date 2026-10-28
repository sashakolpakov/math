import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorSignReduction
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

/-! # Known Exterior Cohomology -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology.CM

noncomputable section

/-!
# The established exterior-cohomology theorem, anchored to cup products

The comparison is required to send every wedge to its actual iterated
singular cup product. Its Hodge compatibility refers to the project's
canonical coefficient map and pure-form Betti subspaces. Thus the
interface cannot be witnessed by an arbitrary vector-space isomorphism.

Source: Milne, *Hodge classes on abelian varieties*, §1.2(a--b).
The proposition is an explicit prerequisite, not an axiom.
-/

open scoped TensorProduct Classical

namespace AbelianVariety

/-- Iterated cup product of actual rational `H¹` classes, including the
canonical unit for the empty product. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalH1Cup (A : CMAbelianVariety.CM.AbelianVariety) :
    (n : ℕ) → (Fin n → A.variety.rationalCohomology 1) →
      A.variety.rationalCohomology n
  | 0, _ => AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (Betti.Scheme.schemePointSpace A.toOver)
  | n + 1, v => AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1
      (A.rationalH1Cup n (Fin.init v)) (v (Fin.last n))

end AbelianVariety

/-- The classical exterior description with its canonical cup-product
normalization and induced Hodge types. No cycle-algebraicity is included. -/
structure AbelianExteriorComparison (A : CMAbelianVariety.CM.AbelianVariety)
    (H : WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)) where
  rational : ∀ n, (⋀[ℚ]^n (A.variety.rationalCohomology 1)) ≃ₗ[ℚ]
    A.variety.rationalCohomology n
  wedge : ∀ n v, rational n (exteriorPower.ιMulti ℚ n v) = A.rationalH1Cup n v
  pure : ∀ p q x,
    CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) (p + q)
      ((rational (p + q)).toLinearMap.baseChange ℂ x) ∈
        A.variety.pureBettiSubspace p q ↔ x ∈ H.exteriorPureSubspace p q

namespace KnownResults

/-- Cohomology of a complex abelian variety is canonically the exterior
algebra of its `H¹`, with the induced Hodge types. -/
def AbelianExteriorCohomology : Prop :=
  ∀ (A : CMAbelianVariety.CM.AbelianVariety) (H : WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)),
    H.holomorphic = A.h1Holomorphic → H.antiholomorphic = A.h1Antiholomorphic →
      Nonempty (AbelianExteriorComparison A H)

end KnownResults

namespace AbelianExteriorComparison

variable {A : CMAbelianVariety.CM.AbelianVariety}
  {H : WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
  (C : AbelianExteriorComparison A H)

/-- Agreement on actual cup products makes the rational comparison unique. -/
theorem rational_unique (C' : AbelianExteriorComparison A H) (n : ℕ) :
    C.rational n = C'.rational n := by
  apply LinearEquiv.toLinearMap_injective
  apply exteriorPower.linearMap_ext
  ext v
  exact (C.wedge n v).trans (C'.wedge n v).symm

/-- The known exterior theorem transfers a genuine rational Hodge class
to the intrinsic exterior Hodge type already treated in Lean. -/
theorem rational_hodge_preimage (p : ℕ) (a : A.variety.rationalCohomology (p + p))
    (ha : a ∈ A.variety.rationalHodgeClasses p) :
    (1 : ℂ) ⊗ₜ[ℚ] (C.rational (p + p)).symm a ∈ H.exteriorPureSubspace p p := by
  apply (C.pure p p _).mp
  change A.variety.rationalCohomologyInclusion (p + p) a ∈
    A.variety.pureBettiSubspace p p at ha
  simpa only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul] using! ha

local instance (D : Decomposition.CM.CMDecomposition H) : LinearOrder D.EmbeddingIndex :=
  linearOrderOfSTO WellOrderingRel

/-- For actual abelian cohomology, every supported monomial of a rational
Hodge class has the proved finite odd-sign switch chain. The only new
prerequisite here is the established exterior-cohomology comparison. -/
theorem rational_hodge_oddSwitchChain (D : Decomposition.CM.CMDecomposition H) (p : ℕ)
    (a : A.variety.rationalCohomology (p + p))
    (ha : a ∈ A.variety.rationalHodgeClasses p)
    (s : D.ExteriorIndex (p + p))
    (hs : (D.exteriorEmbeddingBasis (p + p)).repr
      ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] (C.rational (p + p)).symm a) s ≠ 0) :
    OddSignSwitch.CM.OddSwitchChain
      (fun i : Fin p => D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s (Fin.castAdd p i)))
      (fun i : Fin p =>
        (D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s (Fin.natAdd p i))).neg) :=
  D.rational_exterior_hodge_oddSwitchChain p ((C.rational (p + p)).symm a)
    (C.rational_hodge_preimage p a ha) s hs

end AbelianExteriorComparison

end

end OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology.CM
