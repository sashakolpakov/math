import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilValues
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationWeilNaturality

/-! # Pairing Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairingValue

noncomputable section

/-! Actual native Tate points are functorial. Equality of finite
Weil values passes to the chosen common residue coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
section Points
variable {S : Scheme.{u}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (f : A ⟶ B) [IsMonHom f] (T : Over S) (q : ℕ) [Fact q.Prime]

theorem nativeTatePoint_map (n : ℕ) (v : Add.schemeTateModule A T q) :
    WeilValues.nativeTatePoint B T q n (Add.schemeTateMap A T q f v) =
      WeilValues.nativeTatePoint A T q n v ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) f := by
  apply (cancel_mono (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B (q ^ n))).mp
  rw [PolarizationWeilNaturality.nativeTorsionPoint_map_inclusion, WeilValues.nativeTatePoint_inclusion, WeilValues.nativeTatePoint_inclusion]
  rfl

end Points

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  (A B : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (q : ℕ) [Fact q.Prime] (n : ℕ)
  (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n))
    (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n))
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
  (e' : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n))
    (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n))
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
  (x y : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q)
  (x' y' : Add.schemeTateModule B (Over.mk (𝟙 (Spec (.of k)))) q) (m : ℕ)

theorem tateBicharacterResidues_eq_nsmul_of_values
    (he : e.pairValue (WeilValues.nativeTatePoint A _ q n x) (WeilValues.nativeTatePoint A _ q n y) =
      (e'.pairValue (WeilValues.nativeTatePoint B _ q n x') (WeilValues.nativeTatePoint B _ q n y')) ^ m) :
    TorsionPairingCoordinates.tateBicharacterResidues A A q n e x y = m • TorsionPairingCoordinates.tateBicharacterResidues B B q n e' x' y' := by
  have hu : BicharacterTorsionValues.finiteTorsionUnitValues A A q n e (Evaluation.Tate.evaluate q n x) (Evaluation.Tate.evaluate q n y) =
      m • BicharacterTorsionValues.finiteTorsionUnitValues B B q n e' (Evaluation.Tate.evaluate q n x') (Evaluation.Tate.evaluate q n y') := by
    change (BicharacterTorsionValues.finiteTorsionUnitValues A A q n e _ _).toMul = (BicharacterTorsionValues.finiteTorsionUnitValues B B q n e' _ _).toMul ^ m
    rw [BicharacterTorsionValues.finiteTorsionUnitValues_value, BicharacterTorsionValues.finiteTorsionUnitValues_value, ← map_pow]
    exact congrArg BicharacterTorsionValues.geometricMultiplicativeUnitHom he
  change (RootTorsionCoordinates.rootTorsionEquiv q k n).symm ⟨BicharacterTorsionValues.finiteTorsionUnitValues A A q n e _ _, _⟩ =
    m • (RootTorsionCoordinates.rootTorsionEquiv q k n).symm ⟨BicharacterTorsionValues.finiteTorsionUnitValues B B q n e' _ _, _⟩
  rw [← map_nsmul]
  apply congrArg (RootTorsionCoordinates.rootTorsionEquiv q k n).symm
  exact Subtype.ext hu

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairingValue
