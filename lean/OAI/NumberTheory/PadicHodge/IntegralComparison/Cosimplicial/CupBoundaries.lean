import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupDegrees
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.CohomologyRepresentatives

/-! # Cup Boundaries -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupBoundaries

noncomputable section

/-! The Alexander–Whitney product sends a genuine coboundary and a
cocycle to a genuine coboundary, in every degree. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupDegrees OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.CohomologyRepresentatives

universe u

theorem incoming_zero (C : CochainComplex AddCommGrpCat.{u} ℕ) : (C.sc 0).f = 0 := by
  change C.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  apply C.shape
  change ¬(ComplexShape.up ℕ).prev 0 + 1 = 0
  omega

theorem boundary_succ_iff (C : CochainComplex AddCommGrpCat.{u} ℕ)
    (n : ℕ) (x : C.X (n + 1)) :
    (∃ z : (C.sc (n + 1)).X₁, (C.sc (n + 1)).f z = x) ↔
      ∃ z : C.X n, C.d n (n + 1) z = x := by
  change (∃ z : C.X ((ComplexShape.up ℕ).prev (n + 1)),
    C.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) z = x) ↔ _
  rw [CochainComplex.prev_nat_succ]

variable (A : CosimplicialObject CommRingCat.{u})

theorem differential_cup_of_right_cocycle (p q : ℕ)
    (a : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) (hy : Cup.differential A q y = 0) :
    Cup.differential A (p + q) (Cup.cup A a y) =
      CupDegrees.degreeCast A (by omega : (p + 1) + q = p + q + 1)
        (Cup.cup A (Cup.differential A p a) y) := by
  rw [CupDegrees.differential_cup_cast, hy, CupDegrees.cup_zero_right, map_zero, smul_zero, add_zero]

theorem differential_signed_cup_of_left_cocycle (p q : ℕ)
    (x : A.obj ⦋p⦌) (a : A.obj ⦋q⦌) (hx : Cup.differential A p x = 0) :
    Cup.differential A (p + q) ((-1 : ℤ) ^ p • Cup.cup A x a) =
      Cup.cup A x (Cup.differential A q a) := by
  rw [CupDegrees.differential_zsmul, CupDegrees.differential_cup_cast, hx, CupDegrees.cup_zero_left,
    map_zero, zero_add, smul_smul]
  simp only [← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]
  rfl

theorem boundary_degreeCast_iff {m n : ℕ} (h : m = n) (x : A.obj ⦋m⦌) :
    (∃ z : ((Cup.complex A).sc m).X₁, ((Cup.complex A).sc m).f z = x) ↔
      ∃ z : ((Cup.complex A).sc n).X₁, ((Cup.complex A).sc n).f z = CupDegrees.degreeCast A h x := by
  subst n
  rfl

theorem cocycle_differential {n : ℕ} (x : Additive.CohomologyRepresentatives.cocycles (Cup.complex A) n) :
    Cup.differential A n x.1 = 0 :=
  (Cup.complex_d_apply A n x.1).symm.trans
    ((Additive.CohomologyRepresentatives.mem_cocycles_iff (Cup.complex A) n x.1).mp x.2)

theorem cup_boundary_left (p q : ℕ) (b : ((Cup.complex A).sc p).X₁)
    (y : Additive.CohomologyRepresentatives.cocycles (Cup.complex A) q) :
    ∃ z : ((Cup.complex A).sc (p + q)).X₁,
      ((Cup.complex A).sc (p + q)).f z =
        Cup.cup A (p := p) (q := q) (((Cup.complex A).sc p).f b) y.1 := by
  cases p with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, incoming_zero]
      exact (CupDegrees.cup_zero_left A y.1).symm
  | succ p =>
      obtain ⟨a, ha⟩ := (boundary_succ_iff (Cup.complex A) p
        (((Cup.complex A).sc (p + 1)).f b)).mp ⟨b, rfl⟩
      have ha' : Cup.differential A p a = ((Cup.complex A).sc (p + 1)).f b :=
        (Cup.complex_d_apply A p a).symm.trans ha
      rw [← ha']
      apply (boundary_degreeCast_iff A (by omega : (p + 1) + q = p + q + 1)
        (Cup.cup A (Cup.differential A p a) y.1)).mpr
      apply (boundary_succ_iff (Cup.complex A) (p + q) _).mpr
      refine ⟨Cup.cup A (p := p) (q := q) a y.1, ?_⟩
      refine (Cup.complex_d_apply A (p + q) _).trans ?_
      exact differential_cup_of_right_cocycle A p q a y.1 (cocycle_differential A y)

theorem cup_boundary_right (p q : ℕ) (x : Additive.CohomologyRepresentatives.cocycles (Cup.complex A) p)
    (b : ((Cup.complex A).sc q).X₁) :
    ∃ z : ((Cup.complex A).sc (p + q)).X₁,
      ((Cup.complex A).sc (p + q)).f z =
        Cup.cup A (p := p) (q := q) x.1 (((Cup.complex A).sc q).f b) := by
  cases q with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, incoming_zero]
      exact (CupDegrees.cup_zero_right A x.1).symm
  | succ q =>
      obtain ⟨a, ha⟩ := (boundary_succ_iff (Cup.complex A) q
        (((Cup.complex A).sc (q + 1)).f b)).mp ⟨b, rfl⟩
      have ha' : Cup.differential A q a = ((Cup.complex A).sc (q + 1)).f b :=
        (Cup.complex_d_apply A q a).symm.trans ha
      rw [← ha']
      apply (boundary_succ_iff (Cup.complex A) (p + q) _).mpr
      refine ⟨(-1 : ℤ) ^ p • Cup.cup A (p := p) (q := q) x.1 a, ?_⟩
      refine (Cup.complex_d_apply A (p + q) _).trans ?_
      exact differential_signed_cup_of_left_cocycle A p q x.1 a
        (cocycle_differential A x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupBoundaries
