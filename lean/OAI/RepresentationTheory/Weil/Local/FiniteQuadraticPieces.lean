import OAI.RepresentationTheory.Weil.Local.FiniteQuadraticDyadic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # Finite Quadratic Pieces -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

/-! Finding a nondegenerate piece when no nonzero isotropic element exists. -/

open scoped Classical

variable {A : Type*} [AddCommGroup A]

def FiniteQuadratic.Construction.QuadraticCharacter.HasPhasePiece (q : FiniteQuadratic.Construction.QuadraticCharacter A) : Prop :=
  ∃ H : AddSubgroup A, Nontrivial H ∧ (q.restrict H).Nondegenerate ∧
    ∀ [Fintype H], FunctionsMetaplectic.Construction.phase (q.restrict H).gauss ^ 8 = 1

theorem FiniteQuadratic.Construction.QuadraticCharacter.cyclic_phase_piece (q : FiniteQuadratic.Construction.QuadraticCharacter A) {x : A} (hx : x ≠ 0)
    {n : ℕ} [NeZero n] (hn : addOrderOf x = n)
    (hnd : ((q.restrict (AddSubgroup.zmultiples x)).pullback
      (FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv x hn).toAddMonoidHom).Nondegenerate)
    (hp : ∀ p : FiniteQuadratic.Construction.QuadraticCharacter (ZMod n), p.Nondegenerate → FunctionsMetaplectic.Construction.phase p.gauss ^ 8 = 1) :
    q.HasPhasePiece := by
  let H := AddSubgroup.zmultiples x
  let e := FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv x hn
  refine ⟨H, ⟨⟨⟨x, AddSubgroup.mem_zmultiples x⟩, 0,
    fun h => hx (congrArg Subtype.val h)⟩⟩, ?_, ?_⟩
  · exact ((q.restrict H).nondegenerate_pullback e).mp hnd
  · intro _
    rw [← (q.restrict H).gauss_pullback e]
    exact hp _ hnd

theorem FiniteQuadratic.Construction.QuadraticCharacter.odd_prime_phase_piece (q : FiniteQuadratic.Construction.QuadraticCharacter A) {x : A} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (horder : addOrderOf x = p) (hx : q x ≠ 1) :
    q.HasPhasePiece := by
  let : Fact p.Prime := ⟨hp⟩
  have hx0 : x ≠ 0 := by intro h; apply hx; rw [h, q.map_zero]
  apply q.cyclic_phase_piece hx0 horder
  · exact ((q.restrict _).nondegenerate_pullback _).mpr
      (q.nondegenerate_prime_cyclic hp hp2 horder hx)
  · intro r _
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, r.phase_gauss_zmod_odd p hp2, one_pow]

theorem FiniteQuadratic.Construction.QuadraticCharacter.two_phase_piece (q : FiniteQuadratic.Construction.QuadraticCharacter A) {x : A}
    (horder : addOrderOf x = 2) (hx : q x ^ 2 ≠ 1) : q.HasPhasePiece := by
  have hx0 : x ≠ 0 := by intro h; subst x; simp at horder
  apply q.cyclic_phase_piece hx0 horder
  · apply FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_zmod_two
    change q (FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv x horder 1).val ^ 2 ≠ 1
    rwa [FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv_one]
  · intro r hr
    exact r.phase_gauss_zmod_two (r.gauss_ne_zero hr)

theorem FiniteQuadratic.Construction.QuadraticCharacter.four_phase_piece (q : FiniteQuadratic.Construction.QuadraticCharacter A) {x : A}
    (horder : addOrderOf x = 4) (hx : q x ^ 4 = -1) : q.HasPhasePiece := by
  have hx0 : x ≠ 0 := by intro h; subst x; simp at horder
  apply q.cyclic_phase_piece hx0 horder
  · apply FiniteQuadratic.Construction.QuadraticCharacter.nondegenerate_zmod_four
    change q (FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv x horder 1).val ^ 4 = -1
    rwa [FiniteQuadratic.Construction.QuadraticCharacter.cyclicEquiv_one]
  · intro r hr
    exact r.phase_gauss_zmod_four (r.gauss_ne_zero hr)

theorem FiniteQuadratic.Construction.QuadraticCharacter.anisotropic_two_piece [Fintype A] (q : FiniteQuadratic.Construction.QuadraticCharacter A) (hG : q.gauss ≠ 0)
    (hani : ∀ z, q z = 1 → z = 0) {x : A} (horder : addOrderOf x = 2) :
    q.HasPhasePiece := by
  by_cases hsq : q x ^ 2 = 1
  · have hx0 : x ≠ 0 := by intro h; subst x; simp at horder
    have hqx : q x = -1 := (sq_eq_one_iff.mp hsq).resolve_left (fun h => hx0 (hani x h))
    have hx2 : 2 • x = 0 := horder ▸ addOrderOf_nsmul_eq_zero x
    obtain ⟨y, hy⟩ := q.pairing_witness hG (fun h => hx0 (hani x h))
    obtain ⟨z, r, hz, hb⟩ := q.two_primary_pairing_witness hx2 hy
    have hr : r < 3 := by
      by_contra h
      obtain ⟨w, hw, hqw⟩ := q.isotropic_of_large_two_power hz (by omega)
      exact hw (hani w hqw)
    have hz0 : z ≠ 0 := by intro h; rw [h, (q.polar x).map_zero_eq_one] at hb; norm_num at hb
    interval_cases r
    · have he : z = 0 := by
        have hh := addOrderOf_nsmul_eq_zero z
        simpa [hz] using hh
      exact False.elim (hz0 he)
    · have hz2 : addOrderOf z = 2 := by simpa using hz
      by_cases hs : q z ^ 2 = 1
      · have hqz : q z = -1 := (sq_eq_one_iff.mp hs).resolve_left (fun h => hz0 (hani z h))
        exact q.anisotropic_plane_subgroup hx2 (hz2 ▸ addOrderOf_nsmul_eq_zero z) hqx hqz hb
      · exact q.two_phase_piece hz2 hs
    · have hz4 : addOrderOf z = 4 := by simpa using hz
      have h8 : q z ^ 8 = 1 := by simpa only [hz4, Nat.reduceMul] using q.value_pow_twice_order z
      have hs : q z ^ 4 = -1 := by
        apply (sq_eq_one_iff.mp (show (q z ^ 4) ^ 2 = 1 by rw [← pow_mul]; exact h8)).resolve_left
        intro h
        have he : 2 • z = 0 := hani _ (by simpa only [q.map_nsmul, Nat.reducePow] using h)
        have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
        norm_num [hz4] at hd
      exact q.four_phase_piece hz4 hs
  · exact q.two_phase_piece horder hsq

theorem FiniteQuadratic.Construction.QuadraticCharacter.anisotropic_has_phase_piece [Fintype A] [Nontrivial A] (q : FiniteQuadratic.Construction.QuadraticCharacter A)
    (hG : q.gauss ≠ 0) (hani : ∀ x, q x = 1 → x = 0) : q.HasPhasePiece := by
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt (Fintype.one_lt_card (α := A)))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card (G := A) p hdiv
  by_cases hp2 : p = 2
  · exact q.anisotropic_two_piece hG hani (hx.trans hp2)
  · apply q.odd_prime_phase_piece hp hp2 hx
    intro h
    have h0 := hani x h
    subst x
    exact hp.ne_one (by simpa using hx.symm)

end

end OAI.RepresentationTheory.Weil.Local
