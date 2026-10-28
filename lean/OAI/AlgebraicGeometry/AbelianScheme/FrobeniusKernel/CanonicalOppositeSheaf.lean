import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OppositeSheafAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteSubgroupCommutative

/-! # Canonical Opposite Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOppositeSheaf.Construction

noncomputable section

/-! The constructed native opposite is the annihilator for the original
canonical block pairing, and its second annihilator is the chosen subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] CartierSheafKernels.Construction.representedFppfAbMap_mono

theorem pairing_rightAdjoint_injective {S : Scheme} {G H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e f : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G H) (h : e.rightAdjoint = f.rightAdjoint) : e = f := by
  have hf : e.flip = f.flip := congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk h
  exact e.flip_flip.symm.trans ((congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.flip hf).trans f.flip_flip)

theorem flipped_annihilator_eq_of_pairing_eq {S : Scheme} {G K : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e f : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) (h : e = f) {H : Subobject G} {J : Subobject K}
    (hf : CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator f.flip J = H) : CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.flip J = H :=
  (congrArg (fun b : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K => CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator b.flip J) h).trans hf

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n : ℕ) (τ : Gal(E/ℚ))
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
variable (P : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))

local instance chosenBlockCommutative (σ : Gal(E/ℚ)) :
    IsCommMonObj (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ σ n).X :=
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ n σ).comm

theorem canonicalSheafBlockPairing_eq_sourcePairing :
    CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing j iota hsplit A ρ n τ =
      P.sourceSheafPairing (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P) := by
  apply pairing_rightAdjoint_injective
  exact (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso_character j iota hsplit A ρ n τ hρ hgood P).symm.trans
    (P.sourceSheafPairing_rightAdjoint (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P)).symm

variable (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))

abbrev canonicalOppositeSubgroupSheaf :
    Subobject (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k))
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) n)) :=
  Subobject.mk (P.representedOppositeInclusion H.coordinates H.inclusion
    (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P))

theorem canonicalOppositeSubgroup_annihilator :
    canonicalOppositeSubgroupSheaf j iota hsplit A ρ n τ hρ hgood P H =
      CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator (CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing j iota hsplit A ρ n τ)
        (CartierModel.Construction.CartierCoordinates.representedSubgroup H.inclusion) :=
  (P.sourceSheafPairing_annihilator H.coordinates H.inclusion
    (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P)).symm.trans
    (congrArg (fun e => CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e (CartierModel.Construction.CartierCoordinates.representedSubgroup H.inclusion))
      (canonicalSheafBlockPairing_eq_sourcePairing j iota hsplit A ρ n τ hρ hgood P)).symm

abbrev canonicalOppositeSubgroup_double :=
  flipped_annihilator_eq_of_pairing_eq _ _
    (canonicalSheafBlockPairing_eq_sourcePairing j iota hsplit A ρ n τ hρ hgood P)
    (P.representedOpposite_double H.coordinates H.inclusion
      (CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOppositeSheaf.Construction
