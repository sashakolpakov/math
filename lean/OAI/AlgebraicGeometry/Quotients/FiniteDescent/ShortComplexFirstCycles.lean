import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexEndpointHomotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Short Complex First Cycles -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexFirstCycles.Construction.LocalSectionLifting

noncomputable section

/-! Explicit preservation of degree-zero cycles under a short-complex homotopy. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R] {S T U : ShortComplex (ModuleCat.{v} R)}

def shortComplexFirstCyclesMap (φ : S ⟶ T) : LinearMap.ker S.f.hom →ₗ[R] LinearMap.ker T.f.hom where
  toFun x := ⟨φ.τ₁ x, by
    have h := CategoryTheory.congr_fun φ.comm₁₂ x.val
    change T.f (φ.τ₁ x.val) = φ.τ₂ (S.f x.val) at h
    rw [show S.f x.val = 0 from x.property, map_zero] at h
    exact h⟩
  map_add' x y := Subtype.ext (map_add φ.τ₁.hom x.val y.val)
  map_smul' r x := Subtype.ext (map_smul φ.τ₁.hom r x.val)

theorem shortComplexFirstCyclesMap_id :
    shortComplexFirstCyclesMap (𝟙 S) = LinearMap.id := rfl

theorem shortComplexFirstCyclesMap_comp (φ : S ⟶ T) (ψ : T ⟶ U) :
    shortComplexFirstCyclesMap (φ ≫ ψ) =
      (shortComplexFirstCyclesMap ψ).comp (shortComplexFirstCyclesMap φ) := rfl

theorem shortComplexFirstCyclesMap_homotopy {φ ψ : S ⟶ T}
    (h : ShortComplex.Homotopy φ ψ) (h₀ : h.h₀ = 0) :
    shortComplexFirstCyclesMap φ = shortComplexFirstCyclesMap ψ := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change φ.τ₁ x.val = ψ.τ₁ x.val
  have hc := CategoryTheory.congr_fun h.comm₁ x.val
  change φ.τ₁ x.val = h.h₁ (S.f x.val) + h.h₀ x.val + ψ.τ₁ x.val at hc
  rw [show S.f x.val = 0 from x.property, map_zero, h₀] at hc
  simpa using hc

def shortComplexFirstCyclesEquiv (e : ShortComplex.HomotopyEquiv S T)
    (hh : e.homotopyHomInvId.h₀ = 0) (hi : e.homotopyInvHomId.h₀ = 0) :
    LinearMap.ker S.f.hom ≃ₗ[R] LinearMap.ker T.f.hom :=
  LinearEquiv.ofLinearMap (shortComplexFirstCyclesMap e.hom) (shortComplexFirstCyclesMap e.inv)
    (by
      rw [← shortComplexFirstCyclesMap_comp,
        shortComplexFirstCyclesMap_homotopy e.homotopyInvHomId hi, shortComplexFirstCyclesMap_id])
    (by
      rw [← shortComplexFirstCyclesMap_comp,
        shortComplexFirstCyclesMap_homotopy e.homotopyHomInvId hh, shortComplexFirstCyclesMap_id])

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexFirstCycles.Construction.LocalSectionLifting
