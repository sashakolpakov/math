import OAI.AlgebraicGeometry.PELModuli.CMPoints.InvariantDifferential
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Holomorphic Kernel Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicKernelProjection

noncomputable section

/-! A holomorphic family of surjective matrices has a holomorphic
projection onto its actual kernel on a constructed open neighborhood. -/

open Set _root_.Module
open scoped _root_.Topology

variable {S V W : Type}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] in
theorem exists_holomorphic_kernel_projection
    (p : S → V →L[ℂ] W) (U : Set S) (hU : IsOpen U)
    (hp : DifferentiableOn ℂ p U) (s₀ : S) (hs₀ : s₀ ∈ U)
    (hsurj : Function.Surjective (p s₀)) :
    ∃ (O : Set S) (k : S → V →L[ℂ] V), IsOpen O ∧ s₀ ∈ O ∧ O ⊆ U ∧
      DifferentiableOn ℂ k O ∧ ∀ s ∈ O,
        (k s).range = (p s).ker ∧ ∀ v ∈ (p s).ker, k s v = v := by
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨r₀, hr₀⟩ := (p s₀).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let r := r₀.toContinuousLinearMap
  have hr (v : W) : p s₀ (r v) = v := LinearMap.congr_fun hr₀ v
  let B := fun s => (p s).comp r
  have hB : DifferentiableOn ℂ B U := hp.clm_comp (differentiableOn_const r)
  have hB₀ : B s₀ = (ContinuousLinearEquiv.refl ℂ W).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    exact hr
  obtain ⟨O, D, hO, hsO, hOU, hD, hInv⟩ := InvariantDifferential.exists_holomorphic_inverse_differential_neighborhood
    B U hU (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_nat_of_differentiableOn hU hB 2)
    s₀ hs₀ (ContinuousLinearEquiv.refl ℂ W) hB₀
  let k := fun s => ContinuousLinearMap.id ℂ V - r.comp ((D s).symm.toContinuousLinearMap.comp (p s))
  have hk : DifferentiableOn ℂ k O := (differentiableOn_const (ContinuousLinearMap.id ℂ V)).sub
    ((differentiableOn_const r).clm_comp
      ((hInv.differentiableOn (by norm_num)).clm_comp (hp.mono hOU)))
  have hfix (s : S) (v : V) (hv : v ∈ (p s).ker) : k s v = v := by
    change v - r ((D s).symm (p s v)) = v
    rw [show p s v = 0 from hv, map_zero, map_zero, sub_zero]
  have hker (s : S) (hs : s ∈ O) (v : V) : k s v ∈ (p s).ker := by
    change p s (v - r ((D s).symm (p s v))) = 0
    rw [map_sub]
    have he (w : W) : p s (r w) = D s w :=
      (congrArg (fun f : W →L[ℂ] W => f w) (hD s hs)).symm
    rw [he, ContinuousLinearEquiv.apply_symm_apply, sub_self]
  refine ⟨O, k, hO, hsO, hOU, hk, ?_⟩
  intro s hs
  refine ⟨?_, fun v hv => hfix s v hv⟩
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact hker s hs v
  · intro v hv
    exact ⟨v, hfix s v hv⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicKernelProjection
