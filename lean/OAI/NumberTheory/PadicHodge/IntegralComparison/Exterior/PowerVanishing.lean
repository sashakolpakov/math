import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates

/-! # Power Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.PowerVanishing

noncomputable section

/-! Exterior powers above the length of an actual finite basis vanish,
over arbitrary commutative rings. -/

universe u v
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {n m : ℕ} (b : Module.Basis (Fin n) R V)

include b in
theorem generator_eq_zero (h : n < m) (v : Fin m → V) :
    exteriorPower.ιMulti R m v = 0 := by
  have he : exteriorPower.ιMulti R m (M := V) = 0 := by
    apply b.ext_alternating
    intro f hf
    have hc := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hc
    omega
  rw [he]
  rfl

include b in
theorem eq_zero (h : n < m) (x : ⋀[R]^m V) : x = 0 := by
  have he : (LinearMap.id : (⋀[R]^m V) →ₗ[R] (⋀[R]^m V)) = 0 := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span R m V)
    rintro _ ⟨v, rfl⟩
    exact generator_eq_zero b h v
  exact LinearMap.congr_fun he x

include b in
theorem subsingleton (h : n < m) : Subsingleton (⋀[R]^m V) :=
  ⟨fun x y => (eq_zero b h x).trans (eq_zero b h y).symm⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.PowerVanishing
