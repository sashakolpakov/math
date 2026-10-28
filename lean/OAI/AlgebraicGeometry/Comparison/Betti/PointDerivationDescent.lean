import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Basic.Complex.Basic

/-! # Point Derivation Descent -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PointDerivationDescent

noncomputable section

/-! Point derivations descend through a surjective algebra map when they kill its original kernel. -/

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

theorem pointDerivation_descends
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h) (x : B →ₐ[ℂ] ℂ) :
    let _ : Algebra A ℂ := (x.comp h).toRingHom.toAlgebra
    let _ : Algebra B ℂ := x.toRingHom.toAlgebra
    ∀ D : Derivation ℂ A ℂ, (∀ a, h a = 0 → D a = 0) →
      ∃ D' : Derivation ℂ B ℂ, ∀ a, D' (h a) = D a := by
  let : Algebra A ℂ := (x.comp h).toRingHom.toAlgebra
  let : Algebra B ℂ := x.toRingHom.toAlgebra
  dsimp only
  intro D hD
  have hhl : Function.Surjective h.toLinearMap := hh
  have hk : LinearMap.ker h.toLinearMap ≤ LinearMap.ker D.toLinearMap := fun a ha => hD a ha
  let L : B →ₗ[ℂ] ℂ := ((LinearMap.ker h.toLinearMap).liftQ D.toLinearMap hk).comp
    (h.toLinearMap.quotKerEquivOfSurjective hhl).symm.toLinearMap
  have hL (a : A) : L (h a) = D a := by
    change ((LinearMap.ker h.toLinearMap).liftQ D.toLinearMap hk)
      ((h.toLinearMap.quotKerEquivOfSurjective hhl).symm (h.toLinearMap a)) = D a
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  let D' : Derivation ℂ B ℂ :=
    { toLinearMap := L
      map_one_eq_zero' := by
        change L 1 = 0
        exact (congrArg L h.map_one.symm).trans ((hL 1).trans D.map_one_eq_zero)
      leibniz' := fun b c => by
        obtain ⟨a, rfl⟩ := hh b
        obtain ⟨a', rfl⟩ := hh c
        change L (h a * h a') = x (h a) * L (h a') + x (h a') * L (h a)
        rw [← map_mul, hL, hL, hL]
        exact D.leibniz a a' }
  exact ⟨D', hL⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.PointDerivationDescent
