import OAI.NumberTheory.ArithmeticGroups.Lattices.SiegelReflectionBound
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.RealCoordinates

/-! # Finite Tensor Siegel Cover -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteTensorSiegelCover.Construction

noncomputable section

section

/-! Integral points of the orbit in a Siegel region form a finite set,
once the diagonal and compact-conjugation data have been supplied. -/

open Set MulAction
open scoped Pointwise

theorem siegel_reflection_integral_points_finite
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
    (hdiag : ∀ a ∈ A, ∀ w : V, ∀ i, e (a⁻¹ • w) i = χ a i * e w i) :
    (((fun g : G => g • v) '' (N * A * K)) ∩ (e ⁻¹' Integral.RealCoordinates.Construction.integralRealCoordinates ι)).Finite := by
  obtain ⟨R, hR⟩ := SiegelReflectionBound.Construction.siegel_reflection_orbit_bound e v hv θ hθc hθv
    N A K D D₂ hN hK hD hD₂ hconj hconj₂ hθa hθk χ hdiag 1 zero_lt_one
  apply Integral.RealCoordinates.Construction.integral_coordinates_finite_of_bounded e _ R _ (fun _ hx => hx.2)
  rintro w ⟨⟨g, ⟨_, ⟨n, hn, a, ha, rfl⟩, k, hk, rfl⟩, rfl⟩, hint⟩
  exact hR n hn a ha k hk (Integral.RealCoordinates.Construction.integralRealCoordinates_gap _ hint)

end

/-! Finitely many integral tensor values turn ambient lattice reduction
into finitely many translates modulo the tensor's arithmetic stabilizer. -/

open Set MulAction

theorem stabilizer_finite_siegel_translates
    {G V : Type*} [Group G] [MulAction G V]
    (Γ : Subgroup G) (v : V) (a : G) (S : Set G)
    (hcover : ∀ g : G, g • v = v → ∃ γ ∈ Γ, a * g * γ ∈ S)
    (hfinite : (((fun s : G => s⁻¹ • (a • v)) '' S) ∩
      ((fun γ : G => γ⁻¹ • v) '' (Γ : Set G))).Finite) :
    ∃ F : Set G, F.Finite ∧ F ⊆ Γ ∧ ∀ g : G, g • v = v →
      ∃ s ∈ S, ∃ f ∈ F, ∃ δ ∈ Γ, δ • v = v ∧ g = a⁻¹ * s * f⁻¹ * δ := by
  let T := ((fun s : G => s⁻¹ • (a • v)) '' S) ∩
    ((fun γ : G => γ⁻¹ • v) '' (Γ : Set G))
  have hex (t : T) : ∃ γ : G, γ ∈ Γ ∧ γ⁻¹ • v = t.val := t.property.2
  choose f hf hfe using hex
  let : Finite T := hfinite.to_subtype
  refine ⟨Set.range f, Set.finite_range f, ?_, fun g hg => ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hf t
  · obtain ⟨γ, hγ, hs⟩ := hcover g hg
    have hgi : g⁻¹ • v = v := by
      have he := congrArg (fun w => g⁻¹ • w) hg
      simpa only [inv_smul_smul] using he.symm
    have he : (a * g * γ)⁻¹ • (a • v) = γ⁻¹ • v := by
      simp only [mul_inv_rev, mul_smul, inv_smul_smul, hgi]
    let t : T := ⟨γ⁻¹ • v, ⟨⟨a * g * γ, hs, he⟩, ⟨γ, hγ, rfl⟩⟩⟩
    refine ⟨a * g * γ, hs, f t, Set.mem_range_self t,
      f t * γ⁻¹, Γ.mul_mem (hf t) (Γ.inv_mem hγ), ?_, ?_⟩
    · rw [mul_smul, ← show (f t)⁻¹ • v = γ⁻¹ • v from hfe t, smul_inv_smul]
    · group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteTensorSiegelCover.Construction
