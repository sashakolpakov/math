import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.QRSiegelComparison

/-! # QR Basis Comparison -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.QRBasisComparison.Construction

noncomputable section

/-! Ambient translated Siegel comparison allows a different
orthonormal basis for the output chamber and unipotent coordinates. -/

theorem operatorQRSiegelRegion_right_translate_basis_comparison
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b b' : OrthonormalBasis (Fin m) ℝ L) (x : (L →L[ℝ] L)ˣ)
    (t c s : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : (L →L[ℝ] L)ˣ,
      g ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c →
      (∀ i j, i.val + 1 = j.val →
        OperatorQRVal.Construction.operatorQRLogDiagonal b' (g * x) i - OperatorQRVal.Construction.operatorQRLogDiagonal b' (g * x) j ≤ s) →
      g * x ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b' s C := by
  let p := OperatorQRVal.Construction.orthonormalBasisChangeUnit b b'
  obtain ⟨C, hC, hb⟩ := QRSiegelComparison.Construction.operatorQRSiegelRegion_right_translate_comparison b (x * p) t c s ht
  refine ⟨C, hC, fun g hg hs => ?_⟩
  have hcoord := OperatorQRVal.Construction.operatorQR_basis_change b b' (g * x)
  have hs' : ∀ i j, i.val + 1 = j.val →
      OperatorQRVal.Construction.operatorQRLogDiagonal b (g * (x * p)) i - OperatorQRVal.Construction.operatorQRLogDiagonal b (g * (x * p)) j ≤ s := by
    intro i j hij
    rw [← mul_assoc, ← hcoord.1]
    exact hs i j hij
  have hmem := hb g hg hs'
  refine ⟨hs, fun i j => ?_⟩
  rw [hcoord.2, mul_assoc]
  exact hmem.2 i j

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.QRBasisComparison.Construction
