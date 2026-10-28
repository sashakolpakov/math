import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplicative
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.PairingTarget

/-! # Multiplicative Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeAnnihilator.Construction

noncomputable section

/-!
Construct the relative annihilator for a genuine G_m-valued pairing on
torsion. The etale target is now the actual root-of-unity scheme derived
from the pairing, rather than an additional choice in the input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B P : Over S} [GrpObj A] [GrpObj B]

theorem multiplicative_pairing_annihilator_has_model
    (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (n : ℕ) (hA : (𝟙 A) ^ n = 1)
    (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x))
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) [Etale R.toBase.left]
    [IsFinite B.hom] [Etale B.hom] : Nonempty (e.relativeAnnihilator F).Model := by
  let : Etale (Multiplicative.Construction.rootsOfUnityScheme S n).hom := Multiplicative.Construction.rootsOfUnityScheme_etale S n hn
  let : IsSeparated (Multiplicative.Construction.rootsOfUnityScheme S n).hom := Multiplicative.Construction.rootsOfUnityScheme_separated S n
  have hh := (e.torsionTarget n hA).relativeAnnihilator_has_model F R
  rw [Annihilator.Construction.SchemeBicharacter.torsionTarget_relativeAnnihilator] at hh
  exact hh

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeAnnihilator.Construction
