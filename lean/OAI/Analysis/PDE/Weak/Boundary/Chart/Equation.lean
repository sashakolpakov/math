import OAI.Analysis.PDE.Weak.Boundary.Chart.Coefficient
import OAI.Analysis.PDE.Weak.Boundary.H1BoundedChart
import OAI.Analysis.PDE.Weak.Elliptic.SmoothExtension
import OAI.Analysis.PDE.Variational.LocalizedEquation

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem chartCoefficient_gradient
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (y : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hinv : (chartGradientMap P (G y)).comp (chartGradientMap G y) =
      ContinuousLinearMap.id ℝ _) (v : OAI.Analysis.PDE.Variational.CellVectors m) :
    chartCoefficient A G P w y (chartGradientMap G y v) =
      w y • coordinateTangentMap (fderiv ℝ P (G y)) (A (G y) v) := by
  have he : chartGradientMap P (G y) (chartGradientMap G y v) = v :=
    congrArg (fun T => T v) hinv
  simp only [chartCoefficient, smul_apply, ContinuousLinearMap.comp_apply, he]
  rw [chartGradientMap_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

/-- The actual weak divergence equation after a smooth local change of
coordinates. The transformed gradient is supplied by the bounded H¹
pullback, and no differentiability of the weak solution is assumed. -/
theorem chart_weakDivergenceEquation
    {U V Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hVb : Bornology.IsBounded V)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ y ∈ U, P (G y) = y) (hGP : ∀ z ∈ V, G (P z) = z)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (p q : H1Pair m) (f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hw : ∀ y ∈ U, w y = |(fderiv ℝ G y).det|)
    (hq : ∀ᵐ y ∂volume, y ∈ U → q.2 y = chartGradientMap G y (p.2 (G y)))
    (he : WeakDivergenceEquation (V ∩ Ω) (fun z => A z (p.2 z)) f) :
    WeakDivergenceEquation (U ∩ G ⁻¹' Ω)
      (fun y => chartCoefficient A G P w y (q.2 y))
      (fun y => w y * f (G y)) := by
  have hmap : MapsTo G (U ∩ G ⁻¹' Ω) (V ∩ Ω) := fun y hy => ⟨hGU hy.1, hy.2⟩
  have hpmap : MapsTo P (V ∩ Ω) (U ∩ G ⁻¹' Ω) := by
    intro z hz
    exact ⟨hPV hz.1, by simpa only [mem_preimage, hGP z hz.1] using hz.2⟩
  have hraw := (weakDivergenceEquation_iff_weakFluxEquation _ _ _).mp he
  have ht := hraw.pullback volume (hU.inter (hΩ.preimage hG.continuous)) (hV.inter hΩ)
    (hVb.subset inter_subset_left) hG hP hmap hpmap
    (fun y hy => hPG y hy.1) (fun z hz => hGP z hz.1)
  have hv : WeakDivergenceEquation (U ∩ G ⁻¹' Ω)
      (fun y => |(fderiv ℝ G y).det| • coordinateTangentMap (fderiv ℝ P (G y))
        (A (G y) (p.2 (G y)))) (fun y => |(fderiv ℝ G y).det| * f (G y)) := by
    apply (weakDivergenceEquation_iff_weakFluxEquation _ _ _).mpr
    exact ht
  apply OAI.Analysis.PDE.Variational.weakEquation_congr_on hv Subset.rfl
  · filter_upwards [hq] with y hy
    intro hyU
    rw [hy hyU.1, chartCoefficient_gradient A G P w y
      (chartGradientMap_inverse hU hV (hG.of_le (by simp)) (hP.of_le (by simp)) hGU hPG hGP hyU.1),
      hw y hyU.1]
  · exact Eventually.of_forall (fun y hy => by rw [hw y hy.1])

end OAI.Analysis.PDE.Weak
