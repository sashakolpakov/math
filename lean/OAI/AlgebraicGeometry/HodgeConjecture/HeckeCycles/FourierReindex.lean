import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMeasure

/-! # Fourier Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FourierReindex.CM

noncomputable section

/-! Fourier transform and self-duality commute with actual coordinate relabeling. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.MeasureTheory
variable {I J K : Type*} [Fintype I] [Fintype J]
  [CommRing K] [TopologicalSpace K] [MeasurableSpace K]

theorem transform (e : I ≃ J) (ψ : AddChar K ℂ) (μ : Measure (J → K))
    (f : (I → K) → ℂ) (x : I → K) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ (μ.map (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm)) f x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ μ (f ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x) := by
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier
  rw [ReindexMeasure.CM.integral_map]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    have hd := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex_dot e x (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y)
    have hy : RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) = y := by
      funext j
      exact congrArg y (e.apply_symm_apply j)
    rw [hy] at hd
    change f (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) * ψ (-(x ⬝ᵥ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y)) =
      f (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) * ψ (-(RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x ⬝ᵥ y))
    rw [hd]

omit [CommRing K] [TopologicalSpace K] [MeasurableSpace K] in
theorem finite_selfDual (e : I ≃ J) (ψ : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ℂ) (μ : Measure (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))
    (hμ : ∀ (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz J) x, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ μ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ μ φ.val) x = φ.val (-x))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ (ReindexMeasure.CM.finiteMeasure e μ)
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ (ReindexMeasure.CM.finiteMeasure e μ) φ.val) x = φ.val (-x) := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ (μ.map (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm))
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ (μ.map (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm)) φ.val) x = _
  rw [transform]
  have hfun : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ (μ.map (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm)) φ.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ μ (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ).val := by
    funext y
    rw [Function.comp_apply, transform]
    have hy : RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) = y := by
      funext j
      exact congrArg y (e.apply_symm_apply j)
    rw [hy]
    rfl
  rw [hfun, hμ]
  change φ.val (fun i => -x (e.symm (e i))) = φ.val (-x)
  simp only [e.symm_apply_apply]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FourierReindex.CM
