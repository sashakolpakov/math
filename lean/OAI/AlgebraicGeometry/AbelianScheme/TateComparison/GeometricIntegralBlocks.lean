import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricSplitFrame
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedSourceDecomposition
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberLattices

/-! # Geometric Integral Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Every geometric fiber has actual integral Tate blocks of rank three.
The frame and its source lattices are constructed, and the full integral
Tate image is their product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s) (h : D.HasIntegralModelGeometry)
  {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def Data.SphericalPELAlbaneseData.geometricBlockLattice (v : Fin s × Bool) : Duality.RankThreeLattice ℤ_[q] ℚ_[q] := by
  have := D.fiberIntegralTateImage_isLattice b x
  exact ⟨D.framedSourceLattice (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x)
    (D.geometricSplitFrame hg hdegree hs h b x) v,
    D.framedSourceLattice_isLattice (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x)
      (D.geometricSplitFrame hg hdegree hs h b x) v⟩

def Data.SphericalPELAlbaneseData.geometricIntegralBlockEquiv (v : Fin s × Bool) :
    D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v ≃ₗ[ℤ_[q]]
      (D.geometricBlockLattice hg hdegree hs h b x v).val :=
  D.framedSourceBlockEquiv hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x)
    (D.geometricSplitFrame hg hdegree hs h b x)
    (D.geometricSplitFrame_equivariant hg hdegree hs h b x) v

include hdegree hs h in
theorem Data.SphericalPELAlbaneseData.geometricIntegralBlock_finrank (v : Fin s × Bool) :
    Module.finrank ℤ_[q]
      (D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v) = 3 := by
  rw [(D.geometricIntegralBlockEquiv hg hdegree hs h b x v).finrank_eq]
  have := (D.geometricBlockLattice hg hdegree hs h b x v).property
  exact Submodule.IsLattice.finrank_of_pi ℚ_[q] _

theorem Data.SphericalPELAlbaneseData.geometricIntegralTateImage_eq_pi :
    Rational.framedIntegralTateImage (D.geometricSplitFrame hg hdegree hs h b x) =
      Submodule.pi Set.univ (fun v => (D.geometricBlockLattice hg hdegree hs h b x v).val) :=
  D.framedIntegralTateImage_eq_pi hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x)
    (D.geometricSplitFrame hg hdegree hs h b x)
    (D.geometricSplitFrame_equivariant hg hdegree hs h b x)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
