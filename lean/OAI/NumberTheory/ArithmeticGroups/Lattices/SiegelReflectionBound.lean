import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ActionBounds
import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalActionSquareBound
import OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitBoundedRepresentatives

/-! # Siegel Reflection Bound -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SiegelReflectionBound.Construction

noncomputable section

/-! The qualitative reflection argument: a coordinate gap and bounded
unipotent conjugates bound the discrete points of a Siegel region in a
closed orbit whose stabilizer is preserved by a Cartan automorphism. -/

open Set MulAction
open scoped Pointwise

theorem siegel_reflection_orbit_bound
    {G V ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [Fintype ι] [MulAction G V] [ContinuousSMul G V]
    (e : V ≃L[ℝ] (ι → ℝ)) (v : V) (hv : IsClosed (orbit G v))
    (θ : G →* G) (hθc : Continuous θ) (hθv : ∀ g : G, g • v = v → θ g • v = v)
    (N A K D D₂ : Set G) (hN : IsCompact N) (hK : IsCompact K)
    (hD : IsCompact D) (hD₂ : IsCompact D₂)
    (hconj : ∀ a ∈ A, ∀ n ∈ N, a⁻¹ * n * a ∈ D)
    (hconj₂ : ∀ a ∈ A, ∀ n ∈ N, a⁻¹ * a⁻¹ * n⁻¹ * a * a ∈ D₂)
    (hθa : ∀ a ∈ A, θ a = a⁻¹) (hθk : ∀ k ∈ K, θ k = k)
    (χ : G → ι → ℝ)
    (hdiag : ∀ a ∈ A, ∀ w : V, ∀ i, e (a⁻¹ • w) i = χ a i * e w i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ n ∈ N, ∀ a ∈ A, ∀ k ∈ K,
      (∀ i, e ((n * a * k) • v) i = 0 ∨ ε ≤ |e ((n * a * k) • v) i|) →
      ‖(n * a * k) • v‖ ≤ R := by
  obtain ⟨R₁, hR₁, hfirst⟩ := Compact.ActionBounds.Construction.compact_orbit_bound (D * K) (hD.mul hK) v
  let R₂ := ‖e.symm.toContinuousLinearMap‖ * ((‖e.toContinuousLinearMap‖ * R₁) ^ 2 / ε)
  obtain ⟨R₃, _, hthird⟩ := Compact.ActionBounds.Construction.compact_action_bound (V := V) D₂ hD₂ R₂
  obtain ⟨R₄, hreflect⟩ := ClosedOrbitBoundedRepresentatives.Construction.closed_orbit_stabilizer_preserving_map_bound θ hθc v hv hθv R₃
  obtain ⟨R, _, hlast⟩ := Compact.ActionBounds.Construction.compact_action_bound (V := V) N hN R₄
  refine ⟨R, fun n hn a ha k hk hgap => ?_⟩
  let w := (n * a * k) • v
  have hw : ‖a⁻¹ • w‖ ≤ R₁ := by
    have he : a⁻¹ • w = ((a⁻¹ * n * a) * k) • v := by
      dsimp only [w]
      simp only [mul_smul]
    rw [he]
    exact hfirst _ ⟨_, hconj a ha n hn, k, hk, rfl⟩
  have hsq : ‖(a⁻¹ * a⁻¹) • w‖ ≤ R₂ :=
    DiagonalActionSquareBound.Construction.diagonal_action_square_bound e a⁻¹ (χ a) (hdiag a ha) w ε R₁ hε hR₁ hgap hw
  have hback : ‖(a⁻¹ * k) • v‖ ≤ R₃ := by
    have he : (a⁻¹ * a⁻¹ * n⁻¹ * a * a) • ((a⁻¹ * a⁻¹) • w) = (a⁻¹ * k) • v := by
      dsimp only [w]
      simp only [← mul_smul]
      congr 1
      group
    rw [← he]
    exact hthird _ (hconj₂ a ha n hn) _ hsq
  have hforward : ‖(a * k) • v‖ ≤ R₄ := by
    have he : θ (a⁻¹ * k) = a * k := by rw [map_mul, map_inv, hθa a ha, hθk k hk, inv_inv]
    rw [← he]
    exact hreflect _ hback
  have he : (n * a * k) • v = n • ((a * k) • v) := by simp only [mul_smul]
  rw [he]
  exact hlast n hn _ hforward

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SiegelReflectionBound.Construction
