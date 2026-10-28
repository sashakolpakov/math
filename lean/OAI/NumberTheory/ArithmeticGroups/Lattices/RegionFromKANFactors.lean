import OAI.NumberTheory.ArithmeticGroups.Lattices.QRChamberFiniteVolume
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation

/-! # Region From KAN Factors -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RegionFromKANFactors.Construction

noncomputable section

/-! Explicit compact, positive diagonal, and upper unipotent
factors satisfy the corresponding ambient QR region bounds. -/

theorem operatorQRSiegelRegion_of_factors
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (t c : ℝ)
    (k a n : (L →L[ℝ] L)ˣ) (d : Fin m → ℝ)
    (hk : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ)
    (hd : ∀ i, 0 < d i) (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d)
    (hn : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val))
    (hgap : ∀ i j, i.val + 1 = j.val → Real.log (d i) - Real.log (d j) ≤ t)
    (hbound : ∀ i j, |ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val i j| ≤ c) :
    k * a * n ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c := by
  have he : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (k * a * n).val =
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val * Matrix.diagonal d * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val := by
    change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (k.val * a.val * n.val) = _
    rw [map_mul, map_mul, ha]
  obtain ⟨_, hdiag, hu⟩ := OperatorQRDiagonalTranslation.Construction.operatorQR_kan_unique b (k * a * n) _ _ d hk hd hn he
  constructor
  · intro i j hij
    change Real.log (OperatorQRBasis.Construction.operatorQRDiagonal b (k * a * n) i) - Real.log (OperatorQRBasis.Construction.operatorQRDiagonal b (k * a * n) j) ≤ t
    rw [hdiag]
    exact hgap i j hij
  · intro i j
    rw [hu]
    exact hbound i j

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RegionFromKANFactors.Construction
