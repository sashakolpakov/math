import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRChamberFiniteVolume

/-! # QR Region Basis Covariance -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRRegionBasisCovariance.Construction

noncomputable section

/-! Changing the orthonormal basis of a QR Siegel region is a
fixed right translation. -/

theorem operatorQRSiegelRegion_basis_covariance
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b b' : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) (t c : ℝ) :
    g * (OperatorQRVal.Construction.orthonormalBasisChangeUnit b b')⁻¹ ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b' t c ↔
      g ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c := by
  let p := OperatorQRVal.Construction.orthonormalBasisChangeUnit b b'
  have hcoord := OperatorQRVal.Construction.operatorQR_basis_change b b' (g * p⁻¹)
  have he : g * p⁻¹ * p = g := by group
  change OperatorQRVal.Construction.operatorQRLogDiagonal b' (g * p⁻¹) = OperatorQRVal.Construction.operatorQRLogDiagonal b (g * p⁻¹ * p) ∧
    OperatorQRVal.Construction.operatorQRUnipotentMatrix b' (g * p⁻¹) = OperatorQRVal.Construction.operatorQRUnipotentMatrix b (g * p⁻¹ * p) at hcoord
  rw [he] at hcoord
  change ((∀ i j, i.val + 1 = j.val → OperatorQRVal.Construction.operatorQRLogDiagonal b' (g * p⁻¹) i -
      OperatorQRVal.Construction.operatorQRLogDiagonal b' (g * p⁻¹) j ≤ t) ∧ ∀ i j, |OperatorQRVal.Construction.operatorQRUnipotentMatrix b' (g * p⁻¹) i j| ≤ c) ↔ _
  rw [hcoord.1, hcoord.2]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRRegionBasisCovariance.Construction
