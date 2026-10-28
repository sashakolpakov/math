import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMorphismParameters
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Family Power -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FamilyPower

noncomputable section

/-! Finite powers of a proper family remain proper and have Noetherian total spaces over a Noetherian base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem properSource_noetherian {X S : Scheme.{u}} [IsNoetherian S] (p : X ⟶ S) [IsProper p] :
    IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟩

theorem finiteFamilyPower_proper {S : Scheme.{u}} (A : Over S) [IsProper A.hom] (n : ℕ) :
    IsProper (FamilyPowers.finiteFamilyPower A n).hom := by
  induction n with
  | zero => exact inferInstanceAs (IsProper (𝟙 S))
  | succ n ih =>
      exact inferInstanceAs (IsProper (pullback.fst A.hom (FamilyPowers.finiteFamilyPower A n).hom ≫ A.hom))

instance finiteConstantMorphismParameter_proper {S : Scheme.{u}} (A : Over S) [IsProper A.hom]
    (I : Type u) [Fintype I] : IsProper (ConstantMorphismParameters.finiteConstantMorphismParameter A I).hom :=
  finiteFamilyPower_proper A (Fintype.card I)

instance finiteConstantMorphismParameter_noetherian {S : Scheme.{u}} [IsNoetherian S]
    (A : Over S) [IsProper A.hom] (I : Type u) [Fintype I] :
    IsNoetherian (ConstantMorphismParameters.finiteConstantMorphismParameter A I).left :=
  properSource_noetherian (ConstantMorphismParameters.finiteConstantMorphismParameter A I).hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FamilyPower
