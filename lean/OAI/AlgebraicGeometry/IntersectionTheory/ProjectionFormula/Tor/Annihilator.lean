import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Linear
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Symmetry
import Mathlib.RingTheory.Regular.Category

/-! # Annihilator -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Annihilator

noncomputable section

/-! Scalars annihilating either input annihilate the actual native Tor
modules. A regular element and the long exact sequence then lower a
vanishing bound by one. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (r : R)

theorem first (h : ∀ x : M, r • x = 0) (n : ℕ)
    (x : (((Tor (ModuleCat R) n).obj M).obj N)) : r • x = 0 := by
  let F := (Tor (ModuleCat R) n).flip.obj N
  have hm : r • 𝟙 M = (0 : M ⟶ M) := by
    ext y
    exact h y
  have ht : r • 𝟙 (F.obj M) = (0 : F.obj M ⟶ F.obj M) := by
    rw [← F.map_id, ← Functor.map_smul, hm, F.map_zero]
  exact congrArg (fun f : F.obj M ⟶ F.obj M => f x) ht

theorem second (h : ∀ y : N, r • y = 0) (n : ℕ)
    (x : (((Tor (ModuleCat R) n).obj M).obj N)) : r • x = 0 := by
  let e := (Symmetry.iso R M N n).toLinearEquiv
  apply e.injective
  rw [map_smul, map_zero]
  exact first R N M r h n (e x)

theorem isZero_of_regular (hm : IsSMulRegular M r) (hn : ∀ y : N, r • y = 0)
    (n : ℕ)
    (hzero : IsZero (((Tor (ModuleCat R) (n + 1)).obj
      (ModuleCat.of R (QuotSMulTop r M))).obj N)) :
    IsZero (((Tor (ModuleCat R) n).obj M).obj N) := by
  let S := M.smulShortComplex r
  have hS : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact hm
  let F := (Tor (ModuleCat R) n).flip.obj N
  have hmap : F.map S.f = r • 𝟙 (F.obj M) := by
    change F.map (r • 𝟙 M) = _
    rw [Functor.map_smul, F.map_id]
  have hmapzero : F.map S.f = 0 := by
    rw [hmap]
    ext x
    exact second R M N r hn n x
  exact (ExactSequence.exact_after_connecting R N S hS n).isZero_of_both_zeros
    (hzero.eq_zero_of_src _) hmapzero

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Annihilator
