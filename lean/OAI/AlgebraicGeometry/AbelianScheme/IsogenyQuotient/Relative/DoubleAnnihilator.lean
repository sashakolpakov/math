import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.Annihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeFlip

/-! # Double Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DoubleAnnihilator.Construction

noncomputable section

/-!
Actual CartierDuality double annihilation for the original relative subgroup over
an arbitrary parameter scheme. The proof retains all original test
schemes and transports the derived equality back through the faithful
parameter comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem relative_double_annihilator_from_perfect_pairing
    {S : Scheme.{u}} (G K : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj K.X]
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (P : Over S) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (R : F.Model)
    (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := K.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (he : e.toSheafPairing.IsPerfect) :
    e.flip.relativeAnnihilator (e.relativeAnnihilator F) = F := by
  apply Parameter.TestComparison.Construction.relativeSubgroupOverParameter_injective G P
  calc
    ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (e.flip.relativeAnnihilator (e.relativeAnnihilator F)) =
        (PairingBaseChange.Construction.nativePairingPullback P.hom K G e.flip).relativeAnnihilator
          (ParameterBaseChange.Construction.relativeSubgroupOverParameter K P (e.relativeAnnihilator F)) :=
      Parameter.AnnihilatorComparison.Construction.relativeParameter_annihilator_comparison K G P (e.relativeAnnihilator F) e.flip
    _ = (PairingBaseChange.Construction.nativePairingPullback P.hom G K e).flip.relativeAnnihilator
        ((PairingBaseChange.Construction.nativePairingPullback P.hom G K e).relativeAnnihilator (ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F)) := by
      rw [PairingBaseChangeFlip.Construction.nativePairingPullback_flip, Parameter.AnnihilatorComparison.Construction.relativeParameter_annihilator_comparison]
    _ = ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F :=
      (Parameter.Annihilator.Construction.relativeParameter_annihilator_from_perfect_pairing G K P F R e he).2

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DoubleAnnihilator.Construction
