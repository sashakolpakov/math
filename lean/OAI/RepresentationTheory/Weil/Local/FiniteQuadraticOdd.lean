import OAI.RepresentationTheory.Weil.Local.FiniteQuadraticOf
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! # Finite Quadratic Odd -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

/-! Odd-characteristic quadratic Gauss sums. -/

open scoped Classical

def FiniteQuadraticOdd.Construction.complexQuadraticChar (F : Type*) [Field F] [Fintype F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem FiniteQuadraticOdd.Construction.sum_square_eq_gaussSum
    {F : Type*} [Field F] [Fintype F]
    (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    (∑ x, ψ (x ^ 2)) = gaussSum (FiniteQuadraticOdd.Construction.complexQuadraticChar F) ψ := by
  have hcard (y : F) : ((Finset.univ.filter (fun x : F => x ^ 2 = y)).card : ℂ) =
      FiniteQuadraticOdd.Construction.complexQuadraticChar F y + 1 := by
    have h := quadraticChar_card_sqrts hF y
    have hs : {x : F | x ^ 2 = y}.toFinset = Finset.univ.filter (fun x : F => x ^ 2 = y) := by
      ext x
      simp
    rw [hs] at h
    change _ = (quadraticChar F y : ℂ) + 1
    exact_mod_cast h
  calc
    _ = ∑ y, ((Finset.univ.filter (fun x : F => x ^ 2 = y)).card : ℂ) * ψ y := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        (Finset.sum_fiberwise' Finset.univ (fun x : F => x ^ 2) (fun y => ψ y)).symm
    _ = ∑ y, FiniteQuadraticOdd.Construction.complexQuadraticChar F y * ψ y + ∑ y, ψ y := by
      simp only [hcard, add_mul, one_mul, Finset.sum_add_distrib]
    _ = _ := by rw [AddChar.sum_eq_zero_of_ne_one hψ, add_zero]; rfl

theorem FiniteQuadraticOdd.Construction.phase_sum_square_fourth
    {F : Type*} [Field F] [Fintype F]
    (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) :
    FunctionsMetaplectic.Construction.phase (∑ x, ψ (x ^ 2)) ^ 4 = 1 := by
  by_cases hψ : ψ = 1
  · simp [hψ, FunctionsMetaplectic.Construction.phase, Fintype.card_ne_zero]
  · rw [FiniteQuadraticOdd.Construction.sum_square_eq_gaussSum hF ψ hψ]
    have hχ : FiniteQuadraticOdd.Construction.complexQuadraticChar F ≠ 1 := by
      exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr
        (quadraticChar_ne_one hF)
    have hquad : (FiniteQuadraticOdd.Construction.complexQuadraticChar F).IsQuadratic :=
      (quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ)
    have hs := gaussSum_sq hχ hquad (AddChar.IsPrimitive.of_ne_one hψ)
    have hsign : FiniteQuadraticOdd.Construction.complexQuadraticChar F (-1) ^ 2 = 1 := by
      change (quadraticChar F (-1) : ℂ) ^ 2 = 1
      exact_mod_cast (quadraticChar_sq_one (F := F) (neg_ne_zero.mpr one_ne_zero))
    have hfour : gaussSum (FiniteQuadraticOdd.Construction.complexQuadraticChar F) ψ ^ 4 = (Fintype.card F : ℂ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs, mul_pow, hsign, one_mul]
    apply FiniteQuadraticOf.Construction.phase_pow_of_positive_power _ 4 ((Fintype.card F : ℝ) ^ 2)
      (sq_pos_of_pos (Nat.cast_pos.mpr Fintype.card_pos))
    exact_mod_cast hfour

theorem FiniteQuadratic.Construction.QuadraticCharacter.polar_half {A : Type*} [AddCommGroup A] (q : FiniteQuadratic.Construction.QuadraticCharacter A)
    (y : A) : q (2 • y) = q.polar (2 • y) y := by
  rw [q.map_nsmul, q.polar.map_nsmul_eq_pow, AddChar.pow_apply, q.polar_self]
  norm_num
  ring

theorem FiniteQuadratic.Construction.QuadraticCharacter.polar_zmod {p : ℕ} [NeZero p] (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod p)) (x y : ZMod p) :
    q.polar x y = q.polar 1 (x * y) := by
  have hx : x.val • (1 : ZMod p) = x := by simp [nsmul_eq_mul]
  calc
    _ = q.polar (x.val • (1 : ZMod p)) y := by rw [hx]
    _ = q.polar 1 (x.val • y) := by
      rw [q.polar.map_nsmul_eq_pow, AddChar.pow_apply, (q.polar 1).map_nsmul_eq_pow]
    _ = _ := by congr 1; simp [nsmul_eq_mul]

theorem FiniteQuadratic.Construction.QuadraticCharacter.zmod_as_square_character (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod p)) : ∃ ψ : AddChar (ZMod p) ℂ, ∀ x, q x = ψ (x ^ 2) := by
  let ψ := (q.polar 1).mulShift ((2 : ZMod p)⁻¹)
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  refine ⟨ψ, fun x => ?_⟩
  have hx : 2 • (x / 2) = x := by
    rw [two_nsmul]
    field_simp
    ring
  have h := q.polar_half (x / 2)
  rw [hx, q.polar_zmod] at h
  rw [h]
  change q.polar 1 (x * (x / 2)) = q.polar 1 ((2 : ZMod p)⁻¹ * x ^ 2)
  congr 1
  ring

theorem FiniteQuadratic.Construction.QuadraticCharacter.phase_gauss_zmod_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod p)) : FunctionsMetaplectic.Construction.phase q.gauss ^ 4 = 1 := by
  obtain ⟨ψ, hψ⟩ := q.zmod_as_square_character p hp
  simp only [FiniteQuadratic.Construction.QuadraticCharacter.gauss, hψ]
  exact FiniteQuadraticOdd.Construction.phase_sum_square_fourth (by rwa [ZMod.ringChar_zmod_n]) ψ

end

end OAI.RepresentationTheory.Weil.Local
