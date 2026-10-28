import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalChosenAnnihilatorPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalIntrinsicPairing

/-! # Chosen Annihilator At Level -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenAnnihilatorAtLevel.Construction

noncomputable section

/-! Double annihilation on the exact pair of labels used by the full
kernel, with the canonical opposite isomorphism at that torsion level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
  (τ τc : Gal(E/ℚ)) (hτc : τc = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) (n : ℕ)
  (P : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
  (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))

theorem canonicalChosenAnnihilator_realizes_atLevel (T : Over (Spec (.of k)))
    (x : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    (∀ (U : Over (Spec (.of k))) (t : U ⟶ T)
      (y : U ⟶ (P.annihilatorGroup H.coordinates H.inclusion).X),
      Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
        (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ U (t ≫ x))
        (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τc U
          (y ≫ (P.oppositeInclusion H.coordinates H.inclusion
            (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood τ τc hτc n P)).hom.hom))) ↔
      ∃ z : T ⟶ H.group.X, z ≫ H.inclusion.hom.hom = x := by
  subst τc
  exact CanonicalChosenAnnihilatorPoints.Construction.canonicalChosenAnnihilator_realizes j iota hsplit A ρ n τ hρ hgood P H T x

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenAnnihilatorAtLevel.Construction
