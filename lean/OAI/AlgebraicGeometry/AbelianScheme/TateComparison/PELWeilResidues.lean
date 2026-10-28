import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricTorsionPairing
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionPairingCoordinates

/-! # PEL Weil Residues -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Finite residue values of the actual polarization pairing, evaluated
on compatible sequences of geometric torsion points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) (n : ℕ)

def Data.SphericalPELAlbaneseData.geometricWeilResidues :=
  TorsionPairingCoordinates.tateBicharacterResidues (D.fiberFamily b x).abelian.scheme
    (D.fiberFamily b x).abelian.scheme q n (D.geometricTorsionPairing hg hgeometry b x n)

theorem Data.SphericalPELAlbaneseData.geometricWeilResidues_smul_left (a : ℤ_[q])
    (v w : Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    D.geometricWeilResidues hg hgeometry b x n (a • v) w =
      PadicInt.toZModPow n a * D.geometricWeilResidues hg hgeometry b x n v w :=
  TorsionPairingCoordinates.tateBicharacterResidues_smul_left _ _ q n _ a v w

theorem Data.SphericalPELAlbaneseData.geometricWeilResidues_smul_right (a : ℤ_[q])
    (v w : Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    D.geometricWeilResidues hg hgeometry b x n v (a • w) =
      PadicInt.toZModPow n a * D.geometricWeilResidues hg hgeometry b x n v w :=
  TorsionPairingCoordinates.tateBicharacterResidues_smul_right _ _ q n _ a v w

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
