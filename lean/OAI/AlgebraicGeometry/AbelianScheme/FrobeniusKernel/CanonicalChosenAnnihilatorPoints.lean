import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOppositeSheaf
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicSheafAnnihilatorPoints

/-! # Canonical Chosen Annihilator Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalChosenAnnihilatorPoints.Construction

noncomputable section

/-! All-test orthogonality against the constructed opposite kernel
recovers the original chosen native subgroup for the canonical pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n : ℕ) (τ : Gal(E/ℚ))
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
variable (P : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
variable (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))

local instance chosenBlockCommutativeForPoints (σ : Gal(E/ℚ)) :
    IsCommMonObj (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ σ n).X :=
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ n σ).comm

abbrev canonicalChosenAnnihilator_sheafPoints :=
  IntrinsicSheafAnnihilatorPoints.Construction.nativeSheafDoubleAnnihilator_membership (CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing j iota hsplit A ρ n τ)
    H.inclusion (P.oppositeInclusion H.coordinates H.inclusion
      (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P))
    (CanonicalOppositeSheaf.Construction.canonicalOppositeSubgroup_double j iota hsplit A ρ n τ hρ hgood P H)

theorem canonicalChosenAnnihilator_realizes (T : Over (Spec (.of k)))
    (x : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    (∀ (U : Over (Spec (.of k))) (t : U ⟶ T)
      (y : U ⟶ (P.annihilatorGroup H.coordinates H.inclusion).X),
      Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
        (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ U (t ≫ x))
        (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) U
          (y ≫ (P.oppositeInclusion H.coordinates H.inclusion
            (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P)).hom.hom))) ↔
      ∃ z : T ⟶ H.group.X, z ≫ H.inclusion.hom.hom = x := by
  refine Iff.trans ?_ (canonicalChosenAnnihilator_sheafPoints j iota hsplit A ρ n τ hρ hgood P H T x)
  apply forall_congr'
  intro U
  apply forall_congr'
  intro t
  apply forall_congr'
  intro y
  exact iff_of_eq (congrArg (fun z => z = 1)
    (CanonicalBlockComponents.Construction.canonicalSheafBlockPairing_value j iota hsplit A ρ n τ U (t ≫ x)
      (y ≫ (P.oppositeInclusion H.coordinates H.inclusion
        (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P)).hom.hom))).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalChosenAnnihilatorPoints.Construction
