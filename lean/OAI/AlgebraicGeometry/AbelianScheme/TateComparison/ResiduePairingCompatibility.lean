import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionPairingCoordinates

/-! # Residue Pairing Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ResiduePairingCompatibility

noncomputable section

/-! Compatible unit-valued finite pairings have compatible residue
coordinates in the single chosen system of primitive roots. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable (q : ℕ) [Fact q.Prime] (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]

theorem rootTorsionEquiv_symm_transition (n : ℕ) (z : Add.Tate.torsion q (Additive kˣ) (n + 1)) :
    ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) (ZMod (q ^ n)) ((RootTorsionCoordinates.rootTorsionEquiv q k (n + 1)).symm z) =
      (RootTorsionCoordinates.rootTorsionEquiv q k n).symm (Add.Tate.transition q n z) := by
  apply (RootTorsionCoordinates.rootTorsionEquiv q k n).injective
  rw [AddEquiv.apply_symm_apply, ← RootTorsionCoordinates.rootTorsionEquiv_transition, AddEquiv.apply_symm_apply]

variable {k}
  (A B : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (n : ℕ)
  (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n))
    (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n))
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
  (e' : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ (n + 1)))
    (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ (n + 1)))
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))

theorem finiteTorsionResiduePairing_compatible
    (x : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) n)
    (y : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ B)) n)
    (x' : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) (n + 1))
    (y' : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ B)) (n + 1))
    (he : q • BicharacterTorsionValues.finiteTorsionUnitValues A B q (n + 1) e' x' y' = BicharacterTorsionValues.finiteTorsionUnitValues A B q n e x y) :
    ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) (ZMod (q ^ n))
      (TorsionPairingCoordinates.finiteTorsionResiduePairing A B q (n + 1) e' x' y') =
        TorsionPairingCoordinates.finiteTorsionResiduePairing A B q n e x y := by
  change ZMod.castHom _ _ ((RootTorsionCoordinates.rootTorsionEquiv q k (n + 1)).symm
    ⟨BicharacterTorsionValues.finiteTorsionUnitValues A B q (n + 1) e' x' y', _⟩) =
      (RootTorsionCoordinates.rootTorsionEquiv q k n).symm ⟨BicharacterTorsionValues.finiteTorsionUnitValues A B q n e x y, _⟩
  rw [rootTorsionEquiv_symm_transition]
  apply congrArg (RootTorsionCoordinates.rootTorsionEquiv q k n).symm
  exact Subtype.ext he

theorem tateBicharacterResidues_compatible
    (x : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q)
    (y : Add.schemeTateModule B (Over.mk (𝟙 (Spec (.of k)))) q)
    (he : q • BicharacterTorsionValues.finiteTorsionUnitValues A B q (n + 1) e'
        (Evaluation.Tate.evaluate q (n + 1) x) (Evaluation.Tate.evaluate q (n + 1) y) =
      BicharacterTorsionValues.finiteTorsionUnitValues A B q n e (Evaluation.Tate.evaluate q n x) (Evaluation.Tate.evaluate q n y)) :
    ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) (ZMod (q ^ n))
      (TorsionPairingCoordinates.tateBicharacterResidues A B q (n + 1) e' x y) =
        TorsionPairingCoordinates.tateBicharacterResidues A B q n e x y :=
  finiteTorsionResiduePairing_compatible q A B n e e' _ _ _ _ he

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ResiduePairingCompatibility
