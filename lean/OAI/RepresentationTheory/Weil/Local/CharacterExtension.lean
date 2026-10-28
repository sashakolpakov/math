import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

/-! # Character Extension -/

namespace OAI.RepresentationTheory.Weil.Local.CharacterExtension.Construction

noncomputable section

/-! Extending a multiplicative function from a sufficiently large coordinate domain of a group. -/

variable {G C : Type*} [Group G] [Group C]
  (Ω : Set G) (c : G → C)
  (hrich : ∀ F : Finset G, ∃ x : G, ∀ g ∈ F, x * g ∈ Ω)
  (hmul : ∀ a b : G, a ∈ Ω → b ∈ Ω → a * b ∈ Ω → c (a * b) = c a * c b)

include hrich hmul in
theorem localCharacter_ratio_eq (g x y : G)
    (hx : x ∈ Ω) (hxg : x * g ∈ Ω) (hy : y ∈ Ω) (hyg : y * g ∈ Ω) :
    (c x)⁻¹ * c (x * g) = (c y)⁻¹ * c (y * g) := by
  classical
  obtain ⟨z, hz⟩ := hrich {1, g, x⁻¹, y⁻¹}
  have hz0 : z ∈ Ω := by simpa only [mul_one] using hz 1 (by simp)
  have hzg : z * g ∈ Ω := hz g (by simp)
  have hzx : z * x⁻¹ ∈ Ω := hz x⁻¹ (by simp)
  have hzy : z * y⁻¹ ∈ Ω := hz y⁻¹ (by simp)
  have h₁ : c z = c (z * x⁻¹) * c x := by
    simpa only [inv_mul_cancel_right] using hmul (z * x⁻¹) x hzx hx (by simpa using hz0)
  have h₂ : c (z * g) = c (z * x⁻¹) * c (x * g) := by
    simpa only [mul_assoc, inv_mul_cancel_left] using
      hmul (z * x⁻¹) (x * g) hzx hxg (by simpa [mul_assoc] using hzg)
  have h₃ : c z = c (z * y⁻¹) * c y := by
    simpa only [inv_mul_cancel_right] using hmul (z * y⁻¹) y hzy hy (by simpa using hz0)
  have h₄ : c (z * g) = c (z * y⁻¹) * c (y * g) := by
    simpa only [mul_assoc, inv_mul_cancel_left] using
      hmul (z * y⁻¹) (y * g) hzy hyg (by simpa [mul_assoc] using hzg)
  have he₁ : (c z)⁻¹ * c (z * g) = (c x)⁻¹ * c (x * g) := by rw [h₁, h₂]; group
  have he₂ : (c z)⁻¹ * c (z * g) = (c y)⁻¹ * c (y * g) := by rw [h₃, h₄]; group
  exact he₁.symm.trans he₂

include hrich hmul in
theorem exists_group_character_extension : ∃ χ : G →* C, ∀ g ∈ Ω, χ g = c g := by
  classical
  have hs (g : G) : ∃ x : G, x ∈ Ω ∧ x * g ∈ Ω := by
    obtain ⟨x, hx⟩ := hrich {1, g}
    exact ⟨x, by simpa only [mul_one] using hx 1 (by simp), hx g (by simp)⟩
  choose s hs₁ hs₂ using hs
  let F : G → C := fun g => (c (s g))⁻¹ * c (s g * g)
  have hf (g x : G) (hx : x ∈ Ω) (hxg : x * g ∈ Ω) : F g = (c x)⁻¹ * c (x * g) :=
    localCharacter_ratio_eq Ω c hrich hmul g (s g) x (hs₁ g) (hs₂ g) hx hxg
  have hFone : F 1 = 1 := by dsimp [F]; simp
  have hFmul (g h : G) : F (g * h) = F g * F h := by
    obtain ⟨x, hx⟩ := hrich {1, g, g * h}
    have hx0 : x ∈ Ω := by simpa only [mul_one] using hx 1 (by simp)
    have hxg : x * g ∈ Ω := hx g (by simp)
    have hxgh : x * (g * h) ∈ Ω := hx (g * h) (by simp)
    rw [hf (g * h) x hx0 hxgh, hf g x hx0 hxg,
      hf h (x * g) hxg (by simpa only [mul_assoc] using hxgh)]
    group
  refine ⟨{ toFun := F, map_one' := hFone, map_mul' := hFmul }, ?_⟩
  intro g hg
  change (c (s g))⁻¹ * c (s g * g) = c g
  rw [hmul (s g) g (hs₁ g) hg (hs₂ g), inv_mul_cancel_left]

end

end OAI.RepresentationTheory.Weil.Local.CharacterExtension.Construction
