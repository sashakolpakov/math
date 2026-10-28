import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Power
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTorsionFactor
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Killed Group Etale -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KilledGroupEtale.Construction

noncomputable section

/-! A flat group of finite presentation killed by an invertible integer
is etale. This applies to the actual Cartier representative over arbitrary
bases, with no reducedness or Noetherian hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTorsionFactor.Construction.Schemes

universe u

theorem flatGroup_etale_of_killed {S : Scheme.{u}} (G : Over S)
    [GrpObj G] [IsCommMonObj G] [Flat G.hom] [LocallyOfFinitePresentation G.hom]
    (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
    (hkill : (𝟙 G : G ⟶ G) ^ n = 1) : Etale G.hom := by
  have hp := TorsionQuotient.Power.PowerGeometry.power_formallyUnramified G n hn
  have he : ((𝟙 G : G ⟶ G) ^ n).left = G.hom ≫ η[G].left :=
    congrArg (fun a : G ⟶ G => a.left) hkill
  have : FormallyUnramified (G.hom ≫ η[G].left) := he ▸ hp
  have : FormallyUnramified G.hom := FormallyUnramified.of_comp G.hom η[G].left
  exact Etale.of_formallyUnramified_of_flat G.hom

theorem cartierRepresentative_etale_of_killed {S : Scheme.{u}} (G : Grp (Over S))
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (n : ℕ)
    (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
    (hkill : ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1) : Etale C.dual.X.hom := by
  have : IsCommMonObj C.dual.X := C.commutative
  have : Flat C.dual.X.hom := C.flat
  have : LocallyOfFinitePresentation C.dual.X.hom := C.finitelyPresented
  apply flatGroup_etale_of_killed C.dual.X n hn
  apply (C.sectionEquiv C.dual.X).injective
  rw [map_pow, map_one]
  exact CartierDuality.CharacterTorsionFactor.Construction.Schemes.characterSection_pow_eq_one G n hkill C.dual.X _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KilledGroupEtale.Construction
