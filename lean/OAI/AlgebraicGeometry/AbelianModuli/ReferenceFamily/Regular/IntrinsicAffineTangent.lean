import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.ChartDerivative
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDerivationChart
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Intrinsic Affine Tangent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent

noncomputable section

section

/-! The constructed derivation comparison passes to every chart in the
actual native regular atlas through its analytic transition map. -/

variable {S : Type*} [CommRing S] [Algebra ℂ S] {n : ℕ}

theorem regularChart_transition_derivations
    (e f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S n)
    (hd : ∀ u ∈ e.target, ∃ d : (Fin n → ℂ) ≃ₗ[ℂ] PointDerivations.pointDerivations (e.symm u),
      ∀ v a, (d v).val a = fderiv ℂ (fun w => e.symm w a) u v)
    (u : Fin n → ℂ) (hu : u ∈ f.target) (hue : f.symm u ∈ e.source) :
    ∃ d : (Fin n → ℂ) ≃ₗ[ℂ] PointDerivations.pointDerivations (f.symm u),
      ∀ v a, (d v).val a = fderiv ℂ (fun w => f.symm w a) u v := by
  obtain ⟨d0, hd0⟩ := hd (e (f.symm u)) (e.map_source hue)
  let t : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofBijective (fderiv ℂ (f.symm.trans e) u).toLinearMap
      (ChartDerivative.regularChart_transition_bijective e f he hf u hu hue)
  refine ⟨t.trans (d0.trans (PointDerivations.pointDerivationsCongr (e.left_inv hue))), ?_⟩
  intro v a
  exact (PointDerivations.pointDerivationsCongr_apply (e.left_inv hue) (d0 (t v)) a).trans
    ((hd0 (t v) a).trans (ChartDerivative.regularChart_transition_eval e f he hf u v hu hue a).symm)

theorem nativeRegularChart_derivations [IsDomain S] [Algebra.Smooth ℂ S]
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S) → ℂ))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hx : x ∈ f.source) :
    ∃ d : (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S) → ℂ) ≃ₗ[ℂ] PointDerivations.pointDerivations x,
      ∀ v a, (d v).val a = fderiv ℂ (fun w => f.symm w a) (f x) v := by
  obtain ⟨e, he, hxe, hd⟩ := Intrinsic.AffineDerivationChart.exists_smoothDomain_derivation_chart x
  have hsource : f.symm (f x) ∈ e.source := (f.left_inv hx).symm ▸ hxe
  obtain ⟨d0, hd0⟩ := regularChart_transition_derivations e f he hf hd (f x) (f.map_source hx) hsource
  refine ⟨d0.trans (PointDerivations.pointDerivationsCongr (f.left_inv hx)), ?_⟩
  intro v a
  exact (PointDerivations.pointDerivationsCongr_apply (f.left_inv hx) (d0 v) a).trans (hd0 v a)

end

/-! The existing native smooth-affine manifold tangent space is
canonically the space of algebra derivations at the actual point. -/

open scoped _root_.Manifold ContDiff

variable {S : Type*} [CommRing S] [Algebra ℂ S] [IsDomain S] [Algebra.Smooth ℂ S]

local notation "Model" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S) → ℂ)

def nativeAffineTangentDerivations (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    TangentSpace 𝓘(ℂ, Model) x ≃ₗ[ℂ] PointDerivations.pointDerivations x :=
  (nativeRegularChart_derivations (chartAt Model x) (chart_mem_atlas _ x) x (mem_chart_source _ x)).choose

theorem nativeAffineTangentDerivations_chart (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
    (v : TangentSpace 𝓘(ℂ, Model) x) (a : S) :
    (nativeAffineTangentDerivations x v).val a =
      fderiv ℂ (fun w => (chartAt Model x).symm w a) (chartAt Model x x) v :=
  (nativeRegularChart_derivations (chartAt Model x) (chart_mem_atlas _ x) x
    (mem_chart_source _ x)).choose_spec v a

theorem contMDiff_affineEvaluation (a : S) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Model) 𝓘(ℂ, ℂ) r (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => x a) := by
  intro x
  apply contMDiffAt_iff_source.mpr
  have he : chartAt Model x ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S) :=
    chart_mem_atlas _ x
  have hd := (he.1 a).contDiffAt ((chartAt Model x).open_target.mem_nhds
    ((chartAt Model x).map_source (mem_chart_source _ x)))
  simpa only [extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
    using hd.of_le (show r ≤ ω from le_top)

theorem mfderiv_affineEvaluation_chart (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (a : S) :
    mfderiv 𝓘(ℂ, Model) 𝓘(ℂ, ℂ) (fun y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => y a) x =
      fderiv ℂ (fun w => (chartAt Model x).symm w a) (chartAt Model x x) := by
  rw [((contMDiff_affineEvaluation a 1).mdifferentiableAt (x := x) one_ne_zero).mfderiv]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    id_eq, Set.range_id, fderivWithin_univ, chartAt_self_eq, OpenPartialHomeomorph.refl_apply]
  rfl

theorem nativeAffineTangentDerivations_apply (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
    (v : TangentSpace 𝓘(ℂ, Model) x) (a : S) :
    (nativeAffineTangentDerivations x v).val a =
      mfderiv 𝓘(ℂ, Model) 𝓘(ℂ, ℂ) (fun y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => y a) x v :=
  (nativeAffineTangentDerivations_chart x v a).trans
    (DFunLike.congr_fun (mfderiv_affineEvaluation_chart x a) v).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.IntrinsicAffineTangent
