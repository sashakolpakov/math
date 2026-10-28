import OAI.Geometry.ComplexTorus.RiemannProjectivity.CauchyExtensionOn
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LocalPreparation

/-! # Local Bounded -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalBounded.Constructions.LocalBoundedExtension

noncomputable section

/-!
# RiemannProjectivity: local bounded extension from a nonzero vertical germ

Isolated zeros choose a zero-free circle in one fiber. Compactness preserves
that circle for nearby base points, and the Cauchy construction extends the
bounded function to an actual open neighborhood of the original point.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

theorem exists_extension_of_vertical_germ {n : ℕ}
    {f g : (Fin n → ℂ) × ℂ → ℂ} {O : Set ((Fin n → ℂ) × ℂ)}
    (hO : IsOpen O) (hg : DifferentiableOn ℂ g O)
    (hf : DifferentiableOn ℂ f (O ∩ {p | g p ≠ 0}))
    {x : Fin n → ℂ} {c : ℂ} (hxc : (x, c) ∈ O)
    (hn : ¬∀ᶠ z in 𝓝 c, g (x, z) = 0)
    {C : ℝ} (hbound : ∀ p ∈ O ∩ {p | g p ≠ 0}, ‖f p‖ ≤ C) :
    ∃ (U : Set ((Fin n → ℂ) × ℂ)) (H : (Fin n → ℂ) × ℂ → ℂ),
      IsOpen U ∧ (x, c) ∈ U ∧ U ⊆ O ∧ DifferentiableOn ℂ H U ∧
      EqOn H f (U ∩ {p | g p ≠ 0}) ∧ ∀ p ∈ U, ‖H p‖ ≤ C := by
  obtain ⟨R, hR, hbase, hboundary⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LocalPreparation.Constructions.Preparation.exists_zero_free_circle hO hg hxc hn
  obtain ⟨A, hA, hxA, hAO, hAn⟩ :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootFamiliesAt.Constructions.RootFamilies.exists_disk_family_neighborhood hO hg.continuousOn hbase hboundary
  obtain ⟨hd, heq, hb⟩ := CauchyExtensionOn.Constructions.CauchyExtension.bounded_extension_on_tube hO hg hf hA hR hAO
    (fun y hy z hz => hAn (y, z) ⟨hy, hz⟩) hbound
  exact ⟨A ×ˢ ball c R, CauchyExtensionOn.Constructions.CauchyExtension.transform f c R,
    hA.prod isOpen_ball, ⟨hxA, mem_ball_self hR⟩,
    fun p hp => hAO ⟨hp.1, ball_subset_closedBall hp.2⟩, hd, heq, hb⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalBounded.Constructions.LocalBoundedExtension
