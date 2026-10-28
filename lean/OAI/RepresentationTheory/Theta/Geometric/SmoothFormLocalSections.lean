import OAI.Analysis.DifferentialForms.Manifold.LocalPullback

/-! # Smooth Form Local Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric.SmoothFormLocalSections

noncomputable section

/-! Smoothness of actual differential forms is reflected by a map
with smooth local sections. All tangent identities use the chain rule. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem rawForm_pullback_localSection {n : ℕ} (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N n)
    (f : M → N) (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) f)
    (U : Opens N) (r : N → M) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hs : ∀ y ∈ U, f (r y) = y) (y : N) (hy : y ∈ U) :
    ((a.pullback (E := E) f).pullback (E := F) r) y = a y := by
  have hdr := ((hr y hy).contMDiffAt (U.isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
  have heq : f ∘ r =ᶠ[𝓝 y] id := Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds hy) hs
  have hd := (mfderiv_comp y (hf (r y)) hdr).symm.trans
    (heq.mfderiv_eq.trans mfderiv_id)
  ext v
  change a (f (r y)) (fun i =>
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (r y) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r y (v i))) = a y v
  have hv : (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (r y)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r y (v i))) = v := by
    funext i
    exact congrArg (fun b : F →L[ℝ] F => b (v i)) hd
  rw [hv, hs y hy]

theorem smoothForm_of_localSections {n : ℕ} (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N n)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (a.pullback (E := E) f) univ)
    (hsections : ∀ y : N, ∃ (U : Opens N) (r : N → M), y ∈ U ∧
      ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U ∧ ∀ z ∈ U, f (r z) = z) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn a univ := by
  intro e he z hz
  obtain ⟨U, r, hy, hr, hs⟩ := hsections (e.symm z)
  have hlocal : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn a U := by
    apply ((a.pullback (E := E) f).pullback_smooth_on U.isOpen isOpen_univ ha r hr
      (fun _ _ => Set.mem_univ _)).congr
    intro y hy
    exact rawForm_pullback_localSection a f (hf.mdifferentiable (by simp)) U r hr hs y hy
  exact (Analysis.DifferentialForms.Manifold.LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart U.isOpen hlocal e he ⟨hz.1, hy⟩).contDiffWithinAt

end

end OAI.RepresentationTheory.Theta.Geometric.SmoothFormLocalSections
