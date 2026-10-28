import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalIntrinsicPairing
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicAnnihilatorPoints

/-! # Canonical Opposite Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOppositePoints.Construction

noncomputable section

/-! The actual native opposite kernel realizes the independently specified
canonical orthogonality condition after every test-scheme restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
variable (τ τc : Gal(E/ℚ)) (hτc : τc = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) (n : ℕ)
variable (P : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
variable (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))

theorem canonicalOppositeKernel_realizes (T : Over (Spec (.of k)))
    (y : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τc n).X) :
    (∃ z : T ⟶ (P.annihilatorGroup H.coordinates H.inclusion).X,
      z ≫ (P.oppositeInclusion H.coordinates H.inclusion
        (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood τ τc hτc n P)).hom.hom = y) ↔
      ∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (h : U ⟶ H.group.X),
        Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
          (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H U h)
          (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τc U (t ≫ y)) := by
  rw [IntrinsicAnnihilatorPoints.Construction.oppositeInclusion_factor_iff]
  constructor
  · intro hz U t h
    exact (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel_orthogonal j iota hsplit A ρ hρ hgood τ τc hτc n P U
      (h ≫ H.inclusion.hom.hom) (t ≫ y)).mp (hz (Over.mk t) h)
  · intro hz U h
    exact (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel_orthogonal j iota hsplit A ρ hρ hgood τ τc hτc n P U.left
      (h ≫ H.inclusion.hom.hom) (U.hom ≫ y)).mpr (hz U.left U.hom h)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOppositePoints.Construction
