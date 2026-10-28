import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationWeilCompatibility
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ResiduePairingCompatibility
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ResidueCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearResidueLimit

/-! # Weil Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilValues

noncomputable section

/-! The actual finite polarization Weil pairings form a compatible
system of residue pairings on the actual Tate module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
section Points
variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (T : Over S) (q : ℕ) [Fact q.Prime]

def nativeTatePoint (n : ℕ) (v : Add.schemeTateModule A T q) : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n) :=
  (IntrinsicTorsionPoints.nativeTorsionPointEquiv A T q n (Evaluation.Tate.evaluate q n v)).toMul

theorem nativeTatePoint_inclusion (n : ℕ) (v : Add.schemeTateModule A T q) :
    nativeTatePoint A T q n v ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A (q ^ n) = (v.val n).val.toMul :=
  IntrinsicTorsionPoints.nativeTorsionPointEquiv_inclusion A T q n _

theorem nativeTatePoint_compatible (n : ℕ) (v : Add.schemeTateModule A T q) :
    (nativeTatePoint A T q (n + 1) v ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A (q ^ (n + 1))) ^ q =
      nativeTatePoint A T q n v ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A (q ^ n) := by
  rw [nativeTatePoint_inclusion, nativeTatePoint_inclusion]
  exact congrArg (fun z => z.val.toMul) (v.property n)

end Points

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (q : ℕ) [Fact q.Prime]
  (hdegree : ∀ (n : ℕ) (s : Spec (.of k)), (q ^ n).Coprime (ell.left.finrank (η[D.abelian].left s)))

def isogenyTateWeilResidues (n : ℕ) :=
  TorsionPairingCoordinates.tateBicharacterResidues A A q n
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) (hdegree n))

omit [CharZero k] in
theorem isogenyTateWeilUnitValues_compatible (n : ℕ)
    (v w : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q) :
    q • BicharacterTorsionValues.finiteTorsionUnitValues A A q (n + 1)
        (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell (q ^ (n + 1)) (pow_pos (Fact.out : q.Prime).pos _) (hdegree _))
        (Evaluation.Tate.evaluate q (n + 1) v) (Evaluation.Tate.evaluate q (n + 1) w) =
      BicharacterTorsionValues.finiteTorsionUnitValues A A q n
        (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricIsogenyTorsionPairing A D ell (q ^ n) (pow_pos (Fact.out : q.Prime).pos _) (hdegree n))
        (Evaluation.Tate.evaluate q n v) (Evaluation.Tate.evaluate q n w) := by
  have h := PolarizationWeilCompatibility.geometricIsogenyTorsionPairing_power_refinement A D ell
    (q ^ n) (pow_pos (Fact.out : q.Prime).pos _) (hdegree n)
    (q ^ (n + 1)) (pow_pos (Fact.out : q.Prime).pos _) (hdegree _) q (pow_succ' q n).symm
    (Over.mk (𝟙 (Spec (.of k))))
    (nativeTatePoint A _ q n v) (nativeTatePoint A _ q n w)
    (nativeTatePoint A _ q (n + 1) v) (nativeTatePoint A _ q (n + 1) w)
    (nativeTatePoint_compatible A _ q n v) (nativeTatePoint_compatible A _ q n w)
  change (BicharacterTorsionValues.finiteTorsionUnitValues A A q (n + 1) _ _ _).toMul ^ q =
    (BicharacterTorsionValues.finiteTorsionUnitValues A A q n _ _ _).toMul
  rw [BicharacterTorsionValues.finiteTorsionUnitValues_value, BicharacterTorsionValues.finiteTorsionUnitValues_value, ← map_pow]
  exact congrArg BicharacterTorsionValues.geometricMultiplicativeUnitHom h

theorem isogenyTateWeilResidues_step (n : ℕ)
    (v w : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q) :
    ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) (ZMod (q ^ n))
      (isogenyTateWeilResidues A D ell q hdegree (n + 1) v w) =
        isogenyTateWeilResidues A D ell q hdegree n v w :=
  ResiduePairingCompatibility.tateBicharacterResidues_compatible q A A n _ _ v w
    (isogenyTateWeilUnitValues_compatible A D ell q hdegree n v w)

theorem isogenyTateWeilResidues_compatible (m n : ℕ) (h : m ≤ n)
    (v w : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q) :
    ZMod.castHom (pow_dvd_pow q h) (ZMod (q ^ m)) (isogenyTateWeilResidues A D ell q hdegree n v w) =
      isogenyTateWeilResidues A D ell q hdegree m v w :=
  ResidueCoordinates.residues_compatible_of_step q (fun r => isogenyTateWeilResidues A D ell q hdegree r v w)
    (fun r => isogenyTateWeilResidues_step A D ell q hdegree r v w) m n h

def isogenyTateWeilPairing :
    Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q →ₗ[ℤ_[q]]
      Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q →ₗ[ℤ_[q]] ℤ_[q] :=
  BilinearResidueLimit.bilinearResidueLimit q (isogenyTateWeilResidues A D ell q hdegree)
    (isogenyTateWeilResidues_compatible A D ell q hdegree)
    (fun n => TorsionPairingCoordinates.tateBicharacterResidues_smul_left A A q n _)
    (fun n => TorsionPairingCoordinates.tateBicharacterResidues_smul_right A A q n _)

theorem isogenyTateWeilPairing_spec
    (v w : Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of k)))) q) (n : ℕ) :
    PadicInt.toZModPow n (isogenyTateWeilPairing A D ell q hdegree v w) =
      isogenyTateWeilResidues A D ell q hdegree n v w :=
  BilinearResidueLimit.bilinearResidueLimit_spec q _ _ _ _ v w n

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilValues
