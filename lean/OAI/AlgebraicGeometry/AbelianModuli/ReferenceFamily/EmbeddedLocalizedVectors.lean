import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocalizedCoefficientDensity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocalizedCoefficientDenominators

/-! # Embedded Localized Vectors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLocalizedVectors

noncomputable section

/-! Actual field-valued vectors in a prescribed affine congruence class
are dense at a complex embedding when one coefficient is nonreal there.
Their coordinates have one common power denominator. -/

variable {E : Type*} [Field E]

def localizedCoefficientRing (b : ℕ) (z : E) : Subring E :=
  Subring.closure {(b : E)⁻¹, z}

theorem localizedCoefficientRing_map (μ : E →+* ℂ) (b : ℕ) (z : E) :
    (localizedCoefficientRing b z).map μ = LocalizedCoefficientDensity.complexLocalizedCoefficientRing b (μ z) := by
  simp [localizedCoefficientRing, LocalizedCoefficientDensity.complexLocalizedCoefficientRing, RingHom.map_closure]

def embeddedLocalizedVectors {I : Type*} (μ : E →+* ℂ)
    (b : ℕ) (z : E) (v₀ : I → E) (m : E) : Set (I → ℂ) :=
  {v | ∃ w : I → E, (∀ i, w i ∈ localizedCoefficientRing b z) ∧
    v = fun i => μ (v₀ i + m * w i)}

theorem embeddedLocalizedVectors_eq {I : Type*} (μ : E →+* ℂ)
    (b : ℕ) (z : E) (v₀ : I → E) (m : E) :
    embeddedLocalizedVectors μ b z v₀ m =
      LocalizedCoefficientDensity.affineCoefficientVectors (LocalizedCoefficientDensity.complexLocalizedCoefficientRing b (μ z))
        (fun i => μ (v₀ i)) (μ m) := by
  classical
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun i => μ (w i), ?_, ?_⟩
    · intro i _
      rw [← localizedCoefficientRing_map μ b z]
      exact ⟨w i, hw i, rfl⟩
    · ext i
      change μ (v₀ i) + μ m * μ (w i) = μ (v₀ i + m * w i)
      rw [map_add, map_mul]
  · rintro ⟨c, hc, hv⟩
    have hi (i : I) : ∃ a ∈ localizedCoefficientRing b z, μ a = c i := by
      apply Subring.mem_map.mp
      rw [localizedCoefficientRing_map μ b z]
      exact hc i (Set.mem_univ i)
    choose w hw he using hi
    refine ⟨w, hw, ?_⟩
    rw [← hv]
    ext i
    change μ (v₀ i) + μ m * c i = μ (v₀ i + m * w i)
    rw [map_add, map_mul, he]

theorem embeddedLocalizedVectors_dense {I : Type*} (μ : E →+* ℂ)
    (b : ℕ) (hb : 2 ≤ b) (z : E) (hz : (μ z).im ≠ 0)
    (v₀ : I → E) (m : E) (hm : m ≠ 0) :
    Dense (embeddedLocalizedVectors μ b z v₀ m) := by
  rw [embeddedLocalizedVectors_eq]
  apply LocalizedCoefficientDensity.affineCoefficientVectors_dense _
    (LocalizedCoefficientDensity.complexLocalizedCoefficientRing_dense b hb (μ z) hz)
  exact fun h => hm (μ.injective (h.trans (map_zero μ).symm))

theorem embeddedLocalizedVectors_common_denominator {I : Type*} [Fintype I]
    (μ : E →+* ℂ) (S : Subring E) (b : ℕ) (hb : (b : E) ≠ 0)
    (z : E) (hz : z ∈ S) (v₀ : I → E) (m : E)
    {v : I → ℂ} (hv : v ∈ embeddedLocalizedVectors μ b z v₀ m) :
    ∃ (n : ℕ) (a : I → S),
      ∀ i, (b : ℂ) ^ n * (v i - μ (v₀ i)) = μ m * μ (a i) := by
  obtain ⟨w, hw, rfl⟩ := hv
  obtain ⟨n, hn⟩ := LocalizedCoefficientDenominators.exists_common_power_mul_mem_of_localized_closure
    S (b : E) z (natCast_mem S b) hb hz w hw
  refine ⟨n, fun i => ⟨(b : E) ^ n * w i, hn i⟩, ?_⟩
  intro i
  simp only [map_add, map_mul, map_pow, map_natCast, add_sub_cancel_left]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLocalizedVectors
