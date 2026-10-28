import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationDescent
import OAI.RepresentationTheory.Theta.Adelic.TensorProjective
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Surjective Representation Smoothness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationSmoothness.CM

noncomputable section

/-! Smoothness descends through the actual surjective intertwining map. -/

open Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationDescent.CM

variable {G V W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (Q : V →ₗ[ℂ] W) (s : W →ₗ[ℂ] V) (hs : ∀ w, Q (s w) = w)
  (ρ : G →* (V ≃ₗ[ℂ] V)) (hk : ∀ g v, Q v = 0 → Q (ρ g v) = 0)
  (hρ : ∀ v, IsOpen {g : G | ρ g v = v})

include hρ in
theorem smooth (w : W) : IsOpen {g : G | SurjectiveRepresentationDescent.CM.action Q s hs ρ hk g w = w} := by
  apply (RepresentationTheory.Theta.Adelic.TensorProjective.Smoothness.vectorStabilizer (SurjectiveRepresentationDescent.CM.action Q s hs ρ hk) w).isOpen_of_mem_nhds
  filter_upwards [(hρ (s w)).mem_nhds (x := 1) (by simp)] with g hg
  change SurjectiveRepresentationDescent.CM.action Q s hs ρ hk g w = w
  calc
    _ = SurjectiveRepresentationDescent.CM.action Q s hs ρ hk g (Q (s w)) := congrArg (SurjectiveRepresentationDescent.CM.action Q s hs ρ hk g) (hs w).symm
    _ = Q (ρ g (s w)) := SurjectiveRepresentationDescent.CM.intertwines Q s hs ρ hk g (s w)
    _ = Q (s w) := congrArg Q hg
    _ = w := hs w

omit [IsTopologicalGroup G] in
theorem conjugate_smooth (e : V ≃ₗ[ℂ] W) (σ : G →* (W ≃ₗ[ℂ] W))
    (hσ : ∀ w, IsOpen {g : G | σ g w = w}) (v : V) :
    IsOpen {g : G | ((RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut e.symm).comp σ) g v = v} := by
  have he : {g : G | ((RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut e.symm).comp σ) g v = v} =
      {g : G | σ g (e v) = e v} := by
    apply Set.ext
    intro g
    change e.symm (σ g (e v)) = v ↔ σ g (e v) = e v
    exact e.symm_apply_eq
  rw [he]
  exact hσ (e v)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationSmoothness.CM
