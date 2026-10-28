import OAI.RepresentationTheory.Weil.Local.FiniteQuadraticOdd
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Finite Quadratic Cyclic -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

/-! Transport and cyclic pieces of finite quadratic characters. -/

open scoped Classical

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def FiniteQuadratic.Construction.QuadraticCharacter.pullback (q : FiniteQuadratic.Construction.QuadraticCharacter B) (f : A →+ B) : FiniteQuadratic.Construction.QuadraticCharacter A where
  toFun x := q (f x)
  polar :=
    { toFun x := (q.polar (f x)).compAddMonoidHom f
      map_zero_eq_one' := by ext y; simp
      map_add_eq_mul' x y := by ext z; simp [q.polar.map_add_eq_mul] }
  map_zero := by simpa using q.map_zero
  map_neg x := by simpa using q.map_neg (f x)
  map_add x y := by simpa using q.map_add (f x) (f y)
  norm_eq_one x := q.norm_eq_one (f x)

theorem FiniteQuadratic.Construction.QuadraticCharacter.gauss_pullback [Fintype A] [Fintype B] (q : FiniteQuadratic.Construction.QuadraticCharacter B) (e : A ≃+ B) :
    (q.pullback e.toAddMonoidHom).gauss = q.gauss :=
  Equiv.sum_comp e.toEquiv q

theorem FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_pullback (q : FiniteQuadratic.Construction.QuadraticCharacter B) (e : A ≃+ B) :
    (q.pullback e.toAddMonoidHom).Nondegenerate ↔ q.Nondegenerate := by
  constructor
  · intro h x hx
    have hz : (q.pullback e.toAddMonoidHom).polar (e.symm x) = 1 := by
      ext y
      change q.polar (e (e.symm x)) (e y) = 1
      rw [e.apply_symm_apply, hx, AddChar.one_apply]
    have ht := congrArg e (h _ hz)
    simpa using ht
  · intro h x hx
    apply e.injective
    rw [e.map_zero]
    apply h
    ext y
    have ht := DFunLike.congr_fun hx (e.symm y)
    change q.polar (e x) (e (e.symm y)) = 1 at ht
    simpa using ht

theorem FiniteQuadratic.Construction.QuadraticCharacter.map_zsmul (q : FiniteQuadratic.Construction.QuadraticCharacter A) (n : ℤ) (x : A) :
    q (n • x) = q x ^ (n.natAbs ^ 2) := by
  cases n with
  | ofNat n => simpa using q.map_nsmul n x
  | negSucc n =>
      change q (-((n + 1 : ℕ) : ℤ) • x) = _
      rw [neg_zsmul, q.map_neg, natCast_zsmul, q.map_nsmul]
      rfl

theorem FiniteQuadratic.Construction.QuadraticCharacter.isotropic_zmultiples (q : FiniteQuadratic.Construction.QuadraticCharacter A) {x : A} (hx : q x = 1) :
    q.Isotropic (AddSubgroup.zmultiples x) := by
  intro y hy
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  rw [q.map_zsmul, hx, one_pow]

def FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv (x : A) {n : ℕ} (hn : addOrderOf x = n) :
    ZMod n ≃+ AddSubgroup.zmultiples x :=
  zmodAddEquivOfGenerator (g := ⟨x, AddSubgroup.mem_zmultiples x⟩)
    (by
      intro y
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp y.property
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, Subtype.ext hm⟩)
    (by rwa [Nat.card_zmultiples])

theorem FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv_one (x : A) {n : ℕ} (hn : addOrderOf x = n) :
    (FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv x hn 1).val = x := by simp [FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv]

theorem FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_zmod_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (q : FiniteQuadratic.Construction.QuadraticCharacter (ZMod p)) (hq : q 1 ≠ 1) : q.Nondegenerate := by
  have hψ : q.polar 1 ≠ 1 := by
    intro h
    have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have ht := q.polar_half ((2 : ZMod p)⁻¹)
    have hh : 2 • (2 : ZMod p)⁻¹ = 1 := by
      simpa only [nsmul_eq_mul, Nat.cast_ofNat] using mul_inv_cancel₀ h2
    rw [hh, h, AddChar.one_apply] at ht
    exact hq ht
  intro x hx
  by_contra hne
  apply (AddChar.IsPrimitive.of_ne_one hψ) hne
  ext y
  change q.polar 1 (x * y) = 1
  rw [← q.polar_zmod, hx, AddChar.one_apply]

theorem FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_prime_cyclic (q : FiniteQuadratic.Construction.QuadraticCharacter A) {x : A} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (horder : addOrderOf x = p) (hx : q x ≠ 1) :
    (q.restrict (AddSubgroup.zmultiples x)).Nondegenerate := by
  let : Fact p.Prime := ⟨hp⟩
  let e := FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv x horder
  apply (FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_pullback _ e).mp
  apply FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_zmod_odd p hp2
  change q (FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv x horder 1).val ≠ 1
  rwa [FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv_one]

end

end OAI.RepresentationTheory.Weil.Local
