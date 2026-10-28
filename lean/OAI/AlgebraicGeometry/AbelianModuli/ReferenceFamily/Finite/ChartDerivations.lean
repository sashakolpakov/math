import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChartDerivationsLinear
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Chart Derivations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ChartDerivations

noncomputable section

/-! Number finite regular chart coordinates while retaining the native
derivative-to-derivation comparison. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
open scoped ContDiff

theorem finiteChart_derivations {S ι : Type*} [CommRing S] [Algebra ℂ S] [Fintype ι]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (g : S)
    (e0 : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ι → ℂ)) (hx : x ∈ e0.source)
    (hs : ∀ y ∈ e0.source, y g ≠ 0)
    (hcoords : ∀ i, ∃ (a : S) (k : ℕ), ∀ y ∈ e0.source, e0 y i = y a / (y g) ^ k)
    (hreg : ∀ a : S, ContDiffOn ℂ ω (fun u => e0.symm u a) e0.target)
    (hdual : ∀ u ∈ e0.target, ∃ d : (ι → ℂ) ≃ Dual.PresentedAlgebra.DualAlgebraPoints (e0.symm u),
      ∀ v a, ((d v).val a).snd = fderiv ℂ (fun w => e0.symm w a) u v) :
    ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin (Fintype.card ι) → ℂ),
      e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S (Fintype.card ι) ∧ x ∈ e.source ∧
      ∀ u ∈ e.target, ∃ d : (Fin (Fintype.card ι) → ℂ) ≃ₗ[ℂ] PointDerivations.pointDerivations (e.symm u),
        ∀ v a, (d v).val a = fderiv ℂ (fun w => e.symm w a) u v := by
  let b : (ι → ℂ) ≃L[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin ι).symm).toContinuousLinearEquiv
  let e := e0.transHomeomorph b.toHomeomorph
  have hreg' : ∀ a : S, ContDiffOn ℂ ω (fun u => e.symm u a) e.target := by
    intro a
    change ContDiffOn ℂ ω (fun u => e0.symm (b.symm u) a) (b.symm ⁻¹' e0.target)
    exact (hreg a).comp b.symm.contDiff.contDiffOn (fun _ hu => hu)
  have he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S (Fintype.card ι) := by
    refine ⟨hreg', g, hs, ?_⟩
    intro i
    obtain ⟨a, k, hak⟩ := hcoords ((Fintype.equivFin ι).symm i)
    exact ⟨a, k, fun y hy => hak y hy⟩
  have hd : ∀ u ∈ e0.target, ∃ d : (ι → ℂ) ≃ₗ[ℂ] PointDerivations.pointDerivations (e0.symm u),
      ∀ v a, (d v).val a = fderiv ℂ (fun w => e0.symm w a) u v := by
    intro u hu
    obtain ⟨d, hd⟩ := hdual u hu
    exact ⟨ChartDerivationsLinear.chartDerivationsLinearEquiv (fun w => e0.symm w) u d hd,
      ChartDerivationsLinear.chartDerivationsLinearEquiv_apply (fun w => e0.symm w) u d hd⟩
  exact ⟨e, he, hx, ChartDerivationsLinear.reindexChart_derivations e0 b hreg hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ChartDerivations
