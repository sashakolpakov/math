import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BicharacterTorsionValues
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RootTorsionCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation

/-! # Torsion Pairing Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionPairingCoordinates

noncomputable section

/-! Root coordinates turn actual finite torsion bicharacters into
biadditive residue pairings. P-adic scalar laws follow from their
finite torsion module structures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

section Additive
variable (q : ℕ) [Fact q.Prime] (n : ℕ)
  {H H' J : Type*} [AddCommGroup H] [AddCommGroup H'] [AddCommGroup J]

def biadditiveTorsionLift (β : H →+ H' →+ J)
    (hβ : ∀ x y, (q ^ n) • β x y = 0) : H →+ H' →+ Add.Tate.torsion q J n where
  toFun x := {
    toFun y := ⟨β x y, hβ x y⟩
    map_zero' := Subtype.ext ((β x).map_zero)
    map_add' y z := Subtype.ext ((β x).map_add y z) }
  map_zero' := by
    ext y
    exact congrArg (fun f : H' →+ J => f y) β.map_zero
  map_add' x z := by
    ext y
    exact congrArg (fun f : H' →+ J => f y) (β.map_add x z)

theorem torsionBiadditive_smul_left
    (β : Add.Tate.torsion q H n →+ Add.Tate.torsion q H' n →+ ZMod (q ^ n))
    (a : ℤ_[q]) (x : Add.Tate.torsion q H n) (y : Add.Tate.torsion q H' n) :
    β (a • x) y = PadicInt.toZModPow n a * β x y := by
  change β (PadicInt.toZModPow n a • x) y = _
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), Nat.cast_smul_eq_nsmul]
  exact (congrArg (fun f => f y) (β.map_nsmul (PadicInt.toZModPow n a).val x)).trans
    (nsmul_eq_mul _ _)

theorem torsionBiadditive_smul_right
    (β : Add.Tate.torsion q H n →+ Add.Tate.torsion q H' n →+ ZMod (q ^ n))
    (a : ℤ_[q]) (x : Add.Tate.torsion q H n) (y : Add.Tate.torsion q H' n) :
    β x (a • y) = PadicInt.toZModPow n a * β x y := by
  change β x (PadicInt.toZModPow n a • y) = _
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), Nat.cast_smul_eq_nsmul]
  exact ((β x).map_nsmul (PadicInt.toZModPow n a).val y).trans (nsmul_eq_mul _ _)

end Additive

universe u
variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  (A B : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (q : ℕ) [Fact q.Prime] (n : ℕ)
  (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n))
    (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n))
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))

def finiteTorsionResiduePairing :
    Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) n →+
      Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ B)) n →+ ZMod (q ^ n) :=
  BicharacterTorsionValues.biadditiveMap_comp
    (biadditiveTorsionLift q n (BicharacterTorsionValues.finiteTorsionUnitValues A B q n e)
      (BicharacterTorsionValues.finiteTorsionUnitValues_killed A B q n e))
    (AddMonoidHom.id _) (AddMonoidHom.id _) (RootTorsionCoordinates.rootTorsionEquiv q k n).symm.toAddMonoidHom

def tateBicharacterResidues :
    Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q →+
      Add.schemeTateModule B (Over.mk (𝟙 (Spec (.of k)))) q →+ ZMod (q ^ n) :=
  BicharacterTorsionValues.biadditiveMap_comp (finiteTorsionResiduePairing A B q n e)
    (Evaluation.Tate.evaluate q n).toAddMonoidHom (Evaluation.Tate.evaluate q n).toAddMonoidHom (AddMonoidHom.id _)

theorem tateBicharacterResidues_smul_left (a : ℤ_[q])
    (x : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q)
    (y : Add.schemeTateModule B (Over.mk (𝟙 (Spec (.of k)))) q) :
    tateBicharacterResidues A B q n e (a • x) y =
      PadicInt.toZModPow n a * tateBicharacterResidues A B q n e x y := by
  change finiteTorsionResiduePairing A B q n e (Evaluation.Tate.evaluate q n (a • x)) (Evaluation.Tate.evaluate q n y) = _
  rw [map_smul]
  exact torsionBiadditive_smul_left q n _ a _ _

theorem tateBicharacterResidues_smul_right (a : ℤ_[q])
    (x : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q)
    (y : Add.schemeTateModule B (Over.mk (𝟙 (Spec (.of k)))) q) :
    tateBicharacterResidues A B q n e x (a • y) =
      PadicInt.toZModPow n a * tateBicharacterResidues A B q n e x y := by
  change finiteTorsionResiduePairing A B q n e (Evaluation.Tate.evaluate q n x) (Evaluation.Tate.evaluate q n (a • y)) = _
  rw [map_smul]
  exact torsionBiadditive_smul_right q n _ a _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionPairingCoordinates
