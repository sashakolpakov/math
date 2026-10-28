import OAI.NumberTheory.ArithmeticGroups.Lattices.QRMatrixReconstruction
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedUpperUnipotentSet
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRChamberFiniteVolume

/-! # QR Siegel Comparison -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.QRSiegelComparison.Construction

noncomputable section

/-! Set-theoretic ambient Siegel comparison for an arbitrary fixed
right translate, expressed directly in continuous QR coordinates. -/

theorem operatorQRSiegelRegion_right_translate_comparison
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (x : (L →L[ℝ] L)ˣ)
    (t c s : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : (L →L[ℝ] L)ˣ,
      g ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c →
      (∀ i j, i.val + 1 = j.val →
        OperatorQRVal.Construction.operatorQRLogDiagonal b (g * x) i - OperatorQRVal.Construction.operatorQRLogDiagonal b (g * x) j ≤ s) →
      g * x ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b s C := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  obtain ⟨C, hC, hb⟩ := QRMatrixReconstruction.Construction.compact_upper_translated_siegel_comparison b (F x)
    (BoundedUpperUnipotentSet.Construction.boundedUpperUnipotentSet m c) (BoundedUpperUnipotentSet.Construction.boundedUpperUnipotentSet_isCompact m c) t s ht
  refine ⟨C, hC, fun g hg hs => ⟨hs, ?_⟩⟩
  let n := QRMatrixReconstruction.Construction.operatorQRUpperElement b g
  let z := QRMatrixReconstruction.Construction.translatedSiegelPoint b (F x) (OperatorQRVal.Construction.operatorQRLogDiagonal b g) n
  obtain ⟨k, hk, he⟩ := QRMatrixReconstruction.Construction.operatorQR_translated_reconstruction b g x
  have hz : g * x = k * z := he
  have hlog : OperatorQRVal.Construction.operatorQRLogDiagonal b (g * x) = OperatorQRVal.Construction.operatorQRLogDiagonal b z := by
    rw [hz, OperatorQRLogTranslation.Construction.operatorQRLogDiagonal_left_orthogonal b k z hk]
  have hU : OperatorQRVal.Construction.operatorQRUnipotentMatrix b (g * x) = OperatorQRVal.Construction.operatorQRUnipotentMatrix b z := by
    rw [hz]
    exact (OperatorQROrthogonalTranslation.Construction.operatorQR_left_orthogonal b k z hk).2.2
  have hn : n ∈ BoundedUpperUnipotentSet.Construction.boundedUpperUnipotentSet m c := by
    intro i j
    change |(OperatorQRVal.Construction.operatorQRUnipotentUnit b g).val i j| ≤ c
    rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val]
    exact hg.2 i j
  have hs' : ∀ i j, i.val + 1 = j.val → OperatorQRVal.Construction.operatorQRLogDiagonal b z i - OperatorQRVal.Construction.operatorQRLogDiagonal b z j ≤ s := by
    intro i j hij
    rw [← hlog]
    exact hs i j hij
  intro i j
  rw [hU]
  exact hb (OperatorQRVal.Construction.operatorQRLogDiagonal b g) hg.1 n hn hs' i j

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.QRSiegelComparison.Construction
