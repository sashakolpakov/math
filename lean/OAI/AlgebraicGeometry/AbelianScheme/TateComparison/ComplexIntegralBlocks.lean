import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexSplitEquivariance
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedSourceDecomposition
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberLattices

/-! # Complex Integral Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexIntegralBlocks.SphericalPELAlbaneseData

noncomputable section

/-! The constructed complex frame gives full rank-three lattices for
every actual integral PEL Tate block, together with their product decomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

local notation "fiberBase" => Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (h : D.HasIntegralModelGeometry) (hs : 0 < s)
  (b : fiberBase ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexBlockLattice (v : Fin s × Bool) : Duality.RankThreeLattice ℤ_[q] ℚ_[q] := by
  have := D.fiberIntegralTateImage_isLattice b x
  exact ⟨D.framedSourceLattice (Over.mk (𝟙 fiberBase)) (D.fiberFamily b x)
    (D.complexSplitFrame hg hdegree hs h b x) v,
    D.framedSourceLattice_isLattice (Over.mk (𝟙 fiberBase)) (D.fiberFamily b x)
      (D.complexSplitFrame hg hdegree hs h b x) v⟩

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexIntegralBlockEquiv (v : Fin s × Bool) :
    D.integralTateBlock hg (Over.mk (𝟙 fiberBase)) (D.fiberFamily b x) v ≃ₗ[ℤ_[q]]
      (D.complexBlockLattice hg hdegree h hs b x v).val :=
  D.framedSourceBlockEquiv hg (Over.mk (𝟙 fiberBase)) (D.fiberFamily b x)
    (D.complexSplitFrame hg hdegree hs h b x)
    (D.complexSplitFrame_equivariant hg hdegree hs h b x) v

include hdegree h hs in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexIntegralBlock_finrank (v : Fin s × Bool) :
    Module.finrank ℤ_[q]
      (D.integralTateBlock hg (Over.mk (𝟙 fiberBase)) (D.fiberFamily b x) v) = 3 := by
  rw [(D.complexIntegralBlockEquiv hg hdegree h hs b x v).finrank_eq]
  have := (D.complexBlockLattice hg hdegree h hs b x v).property
  exact Submodule.IsLattice.finrank_of_pi ℚ_[q] _

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexIntegralTateImage_eq_pi :
    Rational.framedIntegralTateImage (D.complexSplitFrame hg hdegree hs h b x) =
      Submodule.pi Set.univ (fun v => (D.complexBlockLattice hg hdegree h hs b x v).val) :=
  D.framedIntegralTateImage_eq_pi hg (Over.mk (𝟙 fiberBase)) (D.fiberFamily b x)
    (D.complexSplitFrame hg hdegree hs h b x)
    (D.complexSplitFrame_equivariant hg hdegree hs h b x)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexIntegralBlocks.SphericalPELAlbaneseData
