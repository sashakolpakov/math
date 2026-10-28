import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.InverseMatrixBounds
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRChamberFiniteVolume

/-! # Siegel QR Bounds -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelQRBounds.Construction

noncomputable section

/-! The standard ambient lattice-reduction region is contained in
the QR Siegel region with logarithmic cutoff log 2 and unit entry bound. -/

theorem boundedSiegelMatrix_qr_bounds
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) (c : ℝ)
    (hg : IntrinsicMatrixKANBounds.Construction.IsBoundedSiegelMatrix (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val) c) :
    g ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b (Real.log 2) c := by
  obtain ⟨K, U, a, hK, ha, hgap, hU, hb, he⟩ := hg
  obtain ⟨_, hdiag, hu⟩ := OperatorQRDiagonalTranslation.Construction.operatorQR_kan_unique b g K U a hK ha hU he
  constructor
  · intro i j hij
    change Real.log (OperatorQRBasis.Construction.operatorQRDiagonal b g i) - Real.log (OperatorQRBasis.Construction.operatorQRDiagonal b g j) ≤ Real.log 2
    rw [hdiag]
    have hlog := Real.log_le_log (ha i) (hgap i j hij)
    rw [Real.log_mul (by norm_num) (ne_of_gt (ha j))] at hlog
    linarith
  · intro i j
    rw [hu]
    exact hb i j

theorem ambient_siegel_inverse_qr_bounds
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (hg : g ∈ (SiegelBracketFiniteness.Construction.ambientSiegelRegion b)⁻¹) :
    g.val ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b (Real.log 2) 1 :=
  boundedSiegelMatrix_qr_bounds b g.val 1 (InverseMatrixBounds.Construction.ambient_siegel_inverse_matrix_bounds b g hg)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelQRBounds.Construction
