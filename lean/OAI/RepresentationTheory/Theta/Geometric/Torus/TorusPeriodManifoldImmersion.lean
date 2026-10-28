import OAI.RepresentationTheory.Theta.Geometric.Torus.RealManifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective
import OAI.RepresentationTheory.Theta.Geometric.Torus.SmoothProjectiveModel

/-! # Torus Period Manifold Immersion -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodManifoldImmersion.CM.Algebraization.PeriodManifoldImmersion

noncomputable section

/-! # GeometricTheta: the period embedding is an immersion in the quotient manifold charts -/

open Set ChartedSpace
open scoped _root_.Manifold

variable (Φ : Data.CM.ProjectivePeriodData)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem mdifferentiableAt_of_projection (f : Φ.periodTorus → W) (q : Φ.periodTorus)
    (h : DifferentiableAt ℂ (fun z : Φ.space => f (QuotientAddGroup.mk z)) (Φ.periodChart q q)) :
    MDifferentiableAt (𝓘(ℂ, Φ.space)) (𝓘(ℂ, W)) f q := by
  apply (mdifferentiableAt_iff_source_of_mem_source (x := q) (Φ.mem_periodChart_source q)).mpr
  simpa only [Φ.period_extChart_symm, Φ.period_extChart, Function.comp_def] using
    h.mdifferentiableAt.mdifferentiableWithinAt

theorem mfderiv_injective_of_projection (f : Φ.periodTorus → W) (q : Φ.periodTorus)
    (hd : DifferentiableAt ℂ (fun z : Φ.space => f (QuotientAddGroup.mk z)) (Φ.periodChart q q))
    (hi : Function.Injective
      (fderiv ℂ (fun z : Φ.space => f (QuotientAddGroup.mk z)) (Φ.periodChart q q))) :
    Function.Injective (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, W)) f q) := by
  let z := Φ.periodChart q q
  have hz : (QuotientAddGroup.mk z : Φ.periodTorus) = q := by
    have h := (Φ.periodChart q).left_inv (Φ.mem_periodChart_source q)
    simpa only [Φ.periodChart_symm] using h
  have hf := mdifferentiableAt_of_projection Φ f q hd
  have hp := (Φ.periodProjection_contMDiff z).mdifferentiableAt (by simp)
  have hfi : MDifferentiableAt (𝓘(ℂ, Φ.space)) (𝓘(ℂ, W)) f (QuotientAddGroup.mk z) := hz ▸ hf
  have hcomp : mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, W))
      (fun z : Φ.space => f (QuotientAddGroup.mk z)) z =
      (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, W)) f q).comp
        (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, Φ.space))
          (QuotientAddGroup.mk : Φ.space → Φ.periodTorus) z) := by
    have h := mfderiv_comp z hfi hp
    rw [hz] at h
    exact h
  have hs : Function.Surjective (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, Φ.space))
      (QuotientAddGroup.mk : Φ.space → Φ.periodTorus) z) := by
    have he : (Φ.periodChart q).MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, Φ.space)) :=
      mdifferentiable_chart q
    have h := he.symm.mfderiv_surjective ((Φ.periodChart q).map_source (Φ.mem_periodChart_source q))
    rw [Φ.periodChart_symm] at h
    exact h
  rw [← mfderiv_eq_fderiv, hcomp] at hi
  change Function.Injective ((mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, W)) f q) ∘
    (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, Φ.space))
      (QuotientAddGroup.mk : Φ.space → Φ.periodTorus) z)) at hi
  exact hi.of_comp_right hs

theorem projective_chart_data {n : ℕ}
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (i : Fin (n + 1)) (q : Φ.periodTorus) (hi : f q ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    MDifferentiableAt (𝓘(ℂ, Φ.space)) (𝓘(ℂ, Fin n → ℂ))
      (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) q ∧
    Function.Injective (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, Fin n → ℂ))
      (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) q) := by
  have hz : (QuotientAddGroup.mk (Φ.periodChart q q) : Φ.periodTorus) = q := by
    have h := (Φ.periodChart q).left_inv (Φ.mem_periodChart_source q)
    simpa only [Φ.periodChart_symm] using h
  have h := hd (Φ.periodChart q q) i (hz.symm ▸ hi)
  exact ⟨mdifferentiableAt_of_projection Φ _ q h.1, mfderiv_injective_of_projection Φ _ q h.1 h.2⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodManifoldImmersion.CM.Algebraization.PeriodManifoldImmersion
