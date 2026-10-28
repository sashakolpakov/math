import OAI.RepresentationTheory.Weil.Local.FiniteQuadraticCyclic
import Mathlib.Data.Nat.Factorization.Basic

/-! # Finite Quadratic Dyadic -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

section

/-! Small dyadic pieces and the two-primary part of a pairing witness. -/

open scoped Classical

variable {A : Type*} [AddCommGroup A]

theorem FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_zmod_two (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod 2)) (hq : q 1 ^ 2 ≠ 1) :
    q.Nondegenerate := by
  intro x hx
  have ht := DFunLike.congr_fun hx 1
  fin_cases x
  · rfl
  · change q.polar 1 1 = 1 at ht
    exact False.elim (hq ((q.polar_self 1).symm.trans ht))

theorem FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_zmod_four (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod 4)) (hq : q 1 ^ 4 = -1) :
    q.Nondegenerate := by
  intro x hx
  have ht := DFunLike.congr_fun hx 1
  change q.polar x 1 = 1 at ht
  have hpow (m : ℕ) : q.polar (m • (1 : ZMod 4)) 1 = (q 1 ^ 2) ^ m := by
    rw [q.polar.map_nsmul_eq_pow, AddChar.pow_apply, q.polar_self]
  fin_cases x
  · rfl
  · change q.polar 1 1 = 1 at ht
    have hs : q 1 ^ 2 = 1 := (q.polar_self 1).symm.trans ht
    have h := congrArg (fun z : ℂ => z ^ 2) hs
    rw [← pow_mul] at h
    norm_num [hq] at h
  · have hs : q 1 ^ 4 = 1 := by
      calc
        _ = q.polar (2 • (1 : ZMod 4)) 1 := by rw [hpow, ← pow_mul]
        _ = 1 := ht
    rw [hq] at hs
    norm_num at hs
  · have hs : q 1 ^ 6 = 1 := by
      calc
        _ = q.polar (3 • (1 : ZMod 4)) 1 := by rw [hpow, ← pow_mul]
        _ = 1 := ht
    have h := congrArg (fun z : ℂ => z ^ 2) hs
    have he : q 1 ^ 12 = -1 := by
      rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, hq]
      norm_num
    rw [← pow_mul, he] at h
    norm_num at h

theorem FiniteQuadratic.Construction.QuadraticCharacter.radical_value_eq_one [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (hq : q.gauss ≠ 0)
    {x : A} (hx : q.polar x = 1) : q x = 1 := by
  have hshift := Equiv.sum_comp (Equiv.addLeft x) q
  change (∑ y, q (x + y)) = q.gauss at hshift
  simp only [q.map_add, hx, AddChar.one_apply, mul_one, ← Finset.mul_sum] at hshift
  exact mul_right_cancel₀ hq (hshift.trans (one_mul q.gauss).symm)

theorem FiniteQuadratic.Construction.QuadraticCharacter.pairing_witness [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (hq : q.gauss ≠ 0)
    {x : A} (hx : q x ≠ 1) : ∃ y, q.polar x y ≠ 1 := by
  by_contra h
  push Not at h
  exact hx (q.radical_value_eq_one hq (by ext y; exact h y))

theorem FiniteQuadratic.Construction.QuadraticCharacter.two_primary_pairing_witness [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A)
    {x y : A} (hx : 2 • x = 0) (hy : q.polar x y ≠ 1) :
    ∃ z : A, ∃ r : ℕ, addOrderOf z = 2 ^ r ∧ q.polar x z = -1 := by
  have hb : q.polar x y = -1 := by
    have hs : q.polar x y ^ 2 = 1 := by
      rw [← AddChar.pow_apply, ← q.polar.map_nsmul_eq_pow, hx]
      simp
    exact (sq_eq_one_iff.mp hs).resolve_left hy
  obtain ⟨r, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (ne_of_gt (addOrderOf_pos y))
  refine ⟨m • y, r, ?_, ?_⟩
  · rw [addOrderOf_nsmul, hn, Nat.gcd_eq_right (by simp), Nat.mul_div_cancel]
    exact hm.pos
  · rw [(q.polar x).map_nsmul_eq_pow, hb, hm.neg_one_pow]

theorem FiniteQuadratic.Construction.QuadraticCharacter.value_pow_twice_order (q : FiniteQuadratic.Construction.QuadraticCharacter A) (x : A) :
    q x ^ (2 * addOrderOf x) = 1 := by
  have h : q.polar (addOrderOf x • x) x = 1 := by simp
  rw [q.polar.map_nsmul_eq_pow, AddChar.pow_apply, q.polar_self, ← pow_mul] at h
  exact h

theorem FiniteQuadratic.Construction.QuadraticCharacter.isotropic_of_large_two_power (q : FiniteQuadratic.Construction.QuadraticCharacter A) {x : A} {r : ℕ}
    (hx : addOrderOf x = 2 ^ r) (hr : 3 ≤ r) : ∃ z : A, z ≠ 0 ∧ q z = 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  have horder : addOrderOf x = 8 * 2 ^ s := by simpa only [pow_add, Nat.reducePow] using hx
  refine ⟨(4 * 2 ^ s) • x, ?_, ?_⟩
  · intro hz
    have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    rw [horder] at hd
    have hh := Nat.le_of_dvd (by positivity : 0 < 4 * 2 ^ s) hd
    have hp : 0 < 2 ^ s := by positivity
    omega
  · rw [q.map_nsmul]
    have he : (4 * 2 ^ s) ^ 2 = (2 * addOrderOf x) * 2 ^ s := by rw [horder]; ring
    rw [he, pow_mul, q.value_pow_twice_order, one_pow]

end

/-! The anisotropic four-element quadratic plane. -/

open scoped Classical

theorem FiniteQuadratic.Construction.QuadraticCharacter.plane_gauss (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod 2 × ZMod 2))
    (h10 : q (1, 0) = -1) (h01 : q (0, 1) = -1) (h11 : q (1, 1) = -1) :
    q.gauss = -2 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [FiniteQuadratic.Construction.QuadraticCharacter.gauss, Fintype.sum_prod_type, hu]
  simp only [Finset.sum_insert (by decide : (0 : ZMod 2) ∉ {(1 : ZMod 2)}), Finset.sum_singleton]
  have h00 : q (0, 0) = 1 := q.map_zero
  rw [h00, h10, h01, h11]
  norm_num

theorem FiniteQuadratic.Construction.QuadraticCharacter.plane_nondegenerate (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod 2 × ZMod 2))
    (h10 : q (1, 0) = -1) (h01 : q (0, 1) = -1) (h11 : q (1, 1) = -1) :
    q.Nondegenerate := by
  have hb : q.polar (1, 0) (0, 1) = -1 := by
    have h := q.map_add (1, 0) (0, 1)
    change q (1, 1) = _ at h
    rw [h11, h10, h01] at h
    simpa using h.symm
  have hd1 : q.polar (1, 0) (1, 0) = 1 := by rw [q.polar_self, h10]; norm_num
  intro ⟨i, j⟩ h
  have ha := DFunLike.congr_fun h (1, 0)
  have hc := DFunLike.congr_fun h (0, 1)
  fin_cases i <;> fin_cases j
  · rfl
  · change q.polar (0, 1) (1, 0) = 1 at ha
    rw [q.polar_symmetric, hb] at ha
    norm_num at ha
  · change q.polar (1, 0) (0, 1) = 1 at hc
    rw [hb] at hc
    norm_num at hc
  · change q.polar ((1, 0) + (0, 1)) (1, 0) = 1 at ha
    rw [q.polar.map_add_eq_mul, AddChar.mul_apply, hd1,
      q.polar_symmetric (0, 1), hb] at ha
    norm_num at ha

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def FiniteQuadratic.Construction.QuadraticCharacter.cyclicTwoHom (x : A) (hx : 2 • x = 0) : ZMod 2 →+ A :=
  ZMod.lift 2 ⟨zmultiplesHom A x, by simpa only [zmultiplesHom_apply, natCast_zsmul] using hx⟩

theorem FiniteQuadratic.Construction.QuadraticCharacter.cyclicTwoHom_one (x : A) (hx : 2 • x = 0) : FiniteQuadratic.Construction.QuadraticCharacter.cyclicTwoHom x hx 1 = x := by
  simpa only [FiniteQuadratic.Construction.QuadraticCharacter.cyclicTwoHom, Int.cast_one, zmultiplesHom_apply, one_zsmul] using!
    (ZMod.lift_coe 2 ⟨zmultiplesHom A x, by
      simpa only [zmultiplesHom_apply, natCast_zsmul] using hx⟩ 1)

def FiniteQuadratic.Construction.QuadraticCharacter.planeHom (x y : A) (hx : 2 • x = 0) (hy : 2 • y = 0) : ZMod 2 × ZMod 2 →+ A :=
  ((FiniteQuadratic.Construction.QuadraticCharacter.cyclicTwoHom x hx).comp (AddMonoidHom.fst _ _)) +
    ((FiniteQuadratic.Construction.QuadraticCharacter.cyclicTwoHom y hy).comp (AddMonoidHom.snd _ _))

theorem FiniteQuadratic.Construction.QuadraticCharacter.planeHom_values (x y : A) (hx : 2 • x = 0) (hy : 2 • y = 0) :
    FiniteQuadratic.Construction.QuadraticCharacter.planeHom x y hx hy (1, 0) = x ∧ FiniteQuadratic.Construction.QuadraticCharacter.planeHom x y hx hy (0, 1) = y ∧
    FiniteQuadratic.Construction.QuadraticCharacter.planeHom x y hx hy (1, 1) = x + y := by
  simp [FiniteQuadratic.Construction.QuadraticCharacter.planeHom, FiniteQuadratic.Construction.QuadraticCharacter.cyclicTwoHom_one]

theorem FiniteQuadratic.Construction.QuadraticCharacter.injective_of_pullback_nondegenerate (q : FiniteQuadratic.Construction.QuadraticCharacter B) (f : A →+ B)
    (h : (q.pullback f).Nondegenerate) : Function.Injective f := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply h
  ext z
  change q.polar (f (x - y)) (f z) = 1
  rw [map_sub, hxy, sub_self, q.polar.map_zero_eq_one, AddChar.one_apply]

def FiniteQuadratic.Construction.QuadraticCharacter.rangeEquiv (f : A →+ B) (hf : Function.Injective f) : A ≃+ f.range :=
  AddEquiv.ofBijective f.rangeRestrict ⟨fun _ _ h => hf (congrArg Subtype.val h), by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩⟩

theorem FiniteQuadratic.Construction.QuadraticCharacter.anisotropic_plane_subgroup (q : FiniteQuadratic.Construction.QuadraticCharacter A) {x y : A}
    (hx : 2 • x = 0) (hy : 2 • y = 0) (hqx : q x = -1) (hqy : q y = -1)
    (hb : q.polar x y = -1) :
    ∃ H : AddSubgroup A, Nontrivial H ∧ (q.restrict H).Nondegenerate ∧
      ∀ [Fintype H], FunctionsMetaplectic.Construction.phase (q.restrict H).gauss ^ 8 = 1 := by
  let f := FiniteQuadratic.Construction.QuadraticCharacter.planeHom x y hx hy
  let p := q.pullback f
  have hv := FiniteQuadratic.Construction.QuadraticCharacter.planeHom_values x y hx hy
  have h10 : p (1, 0) = -1 := by change q (f (1, 0)) = -1; rw [hv.1, hqx]
  have h01 : p (0, 1) = -1 := by change q (f (0, 1)) = -1; rw [hv.2.1, hqy]
  have h11 : p (1, 1) = -1 := by
    change q (f (1, 1)) = -1
    rw [hv.2.2, q.map_add, hqx, hqy, hb]
    norm_num
  have hp := p.plane_nondegenerate h10 h01 h11
  have hf := q.injective_of_pullback_nondegenerate f hp
  let e := FiniteQuadratic.Construction.QuadraticCharacter.rangeEquiv f hf
  have he : (q.restrict f.range).pullback e.toAddMonoidHom = p := rfl
  refine ⟨f.range, e.injective.nontrivial, ?_, ?_⟩
  · exact ((q.restrict f.range).nondegenerate_pullback e).mp (by rwa [he])
  · intro _
    rw [← (q.restrict f.range).gauss_pullback e, he, p.plane_gauss h10 h01 h11]
    norm_num [FunctionsMetaplectic.Construction.phase]

end

end OAI.RepresentationTheory.Weil.Local
