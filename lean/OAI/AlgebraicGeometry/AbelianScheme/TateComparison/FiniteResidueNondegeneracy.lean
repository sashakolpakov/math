import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairingNondegeneracy
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionPairingCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection

/-! # Finite Residue Nondegeneracy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteResidueNondegeneracy

noncomputable section

/-! The actual root-of-unity residue pairing detects finite torsion
points whenever the native sheaf pairing is perfect. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {k : Type u} [Field k]

theorem geometricMultiplicativeUnitHom_injective :
    Function.Injective (BicharacterTorsionValues.geometricMultiplicativeUnitHom (k := k)) :=
  (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom).injective).comp
    (CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective (Over.mk (𝟙 (Spec (.of k)))))

variable [CharZero k] [IsAlgClosed k]
  (A B : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (q : ℕ) [Fact q.Prime] (n : ℕ)
  (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n)) (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n))
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))

theorem finiteTorsionUnitValues_zero_of_residue_zero
    (x : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) n)
    (y : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ B)) n)
    (h : TorsionPairingCoordinates.finiteTorsionResiduePairing A B q n e x y = 0) :
    BicharacterTorsionValues.finiteTorsionUnitValues A B q n e x y = 0 := by
  have hh := congrArg (RootTorsionCoordinates.rootTorsionEquiv q k n) h
  change RootTorsionCoordinates.rootTorsionEquiv q k n ((RootTorsionCoordinates.rootTorsionEquiv q k n).symm
      ⟨BicharacterTorsionValues.finiteTorsionUnitValues A B q n e x y, _⟩) = RootTorsionCoordinates.rootTorsionEquiv q k n 0 at hh
  rw [AddEquiv.apply_symm_apply, map_zero] at hh
  exact congrArg Subtype.val hh

variable [LocallyOfFiniteType (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n)).hom]
  [IsReduced (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n)).left]

theorem finiteTorsionResiduePairing_nondegenerate_left (he : e.toSheafPairing.IsPerfect)
    (x : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) n)
    (hx : ∀ y, TorsionPairingCoordinates.finiteTorsionResiduePairing A B q n e x y = 0) : x = 0 := by
  let T := Over.mk (𝟙 (Spec (.of k)))
  have hp : (IntrinsicTorsionPoints.nativeTorsionPointEquiv A T q n x).toMul = 1 := by
    apply PairingNondegeneracy.schemePairing_geometric_nondegenerate_left e he
    intro y'
    obtain ⟨y, hy⟩ := (IntrinsicTorsionPoints.nativeTorsionPointEquiv B T q n).surjective (Additive.ofMul y')
    have hy' : (IntrinsicTorsionPoints.nativeTorsionPointEquiv B T q n y).toMul = y' := congrArg Additive.toMul hy
    rw [← hy']
    apply geometricMultiplicativeUnitHom_injective
    rw [map_one]
    exact (BicharacterTorsionValues.finiteTorsionUnitValues_value A B q n e x y).symm.trans
      (congrArg Additive.toMul (finiteTorsionUnitValues_zero_of_residue_zero A B q n e x y (hx y)))
  apply (IntrinsicTorsionPoints.nativeTorsionPointEquiv A T q n).injective
  rw [map_zero]
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteResidueNondegeneracy
