import OAI.AlgebraicTopology.Products.SimplexFaceIdentities
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Tactic.Abel

/-! # Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Cup

noncomputable section

/-! The Alexander–Whitney product on the genuine alternating-coface
complex of a cosimplicial ring, with arbitrary ring-map naturality. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.AlgebraicTopology.Products.SimplexFaceIdentities

universe u

variable (A : CosimplicialObject CommRingCat.{u})

def additive : CosimplicialObject AddCommGrpCat.{u} :=
  A ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

def complex : CochainComplex AddCommGrpCat.{u} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).obj (additive A)

def cup {p q : ℕ} (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) : A.obj ⦋p + q⦌ :=
  A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q) x * A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q) y

def differential (n : ℕ) (x : A.obj ⦋n⦌) : A.obj ⦋n + 1⦌ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • A.map (SimplexCategory.δ i) x

theorem complex_d_apply (n : ℕ) (x : A.obj ⦋n⦌) :
    (complex A).d n (n + 1) x = differential A n x := by
  dsimp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  let ev : ((additive A).obj ⦋n⦌ ⟶ (additive A).obj ⦋n + 1⦌) →+
      (additive A).obj ⦋n + 1⦌ :=
    { toFun := fun f => f x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val • (additive A).δ i) Finset.univ

theorem cup_add_left {p q : ℕ} (x x' : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) :
    cup A (x + x') y = cup A x y + cup A x' y := by
  simp only [cup, map_add, add_mul]

theorem cup_add_right {p q : ℕ} (x : A.obj ⦋p⦌) (y y' : A.obj ⦋q⦌) :
    cup A x (y + y') = cup A x y + cup A x y' := by
  simp only [cup, map_add, mul_add]

theorem cup_natural {B : CosimplicialObject CommRingCat.{u}} (f : A ⟶ B)
    {p q : ℕ} (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) :
    f.app ⦋p + q⦌ (cup A x y) = cup B (f.app ⦋p⦌ x) (f.app ⦋q⦌ y) := by
  unfold cup
  rw [map_mul]
  congr 1
  · exact ConcreteCategory.congr_hom (f.naturality (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q)) x
  · exact ConcreteCategory.congr_hom (f.naturality (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q)) y

theorem differential_natural {B : CosimplicialObject CommRingCat.{u}} (f : A ⟶ B)
    (n : ℕ) (x : A.obj ⦋n⦌) :
    f.app ⦋n + 1⦌ (differential A n x) = differential B n (f.app ⦋n⦌ x) := by
  simp only [differential, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact ConcreteCategory.congr_hom (f.naturality (SimplexCategory.δ i)) x

theorem differential_sq (n : ℕ) (x : A.obj ⦋n⦌) :
    differential A (n + 1) (differential A n x) = 0 := by
  rw [← complex_d_apply, ← complex_d_apply]
  exact ConcreteCategory.congr_hom ((complex A).d_comp_d n (n + 1) (n + 1 + 1)) x

theorem coface_cup_left (p q : ℕ) (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌)
    (i : Fin (p + 1)) :
    A.map (SimplexCategory.δ (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.leftFaceIndex p q i)) (cup A x y) =
      A.map (SimplexCategory.subinterval 0 (p + 1) (by omega : 0 + (p + 1) ≤ p + q + 1))
        (A.map (SimplexCategory.δ i.castSucc) x) *
      A.map (SimplexCategory.subinterval (p + 1) q (by omega : (p + 1) + q ≤ p + q + 1)) y := by
  simp only [cup, map_mul]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← A.map_comp, ← A.map_comp, ← A.map_comp,
    OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion_comp_delta_left, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion_comp_delta_left]

theorem coface_cup_right (p q : ℕ) (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌)
    (i : Fin (q + 1)) :
    A.map (SimplexCategory.δ (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.rightFaceIndex p q i)) (cup A x y) =
      A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q + 1)) x *
      A.map (SimplexCategory.subinterval p (q + 1) (by omega : p + (q + 1) ≤ p + q + 1))
        (A.map (SimplexCategory.δ i.succ) y) := by
  simp only [cup, map_mul]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← A.map_comp, ← A.map_comp, ← A.map_comp,
    OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion_comp_delta_right, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion_comp_delta_right]

private theorem alternating_cut {V : Type*} [AddCommGroup V] (p q : ℕ)
    (a : Fin (p + 2) → V) (b : Fin (q + 2) → V)
    (h : a (Fin.last (p + 1)) = b 0) :
    (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • a i.castSucc) +
        (∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • b j.succ) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • a i) +
        (-1 : ℤ) ^ p • (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • b j) := by
  rw [Fin.sum_univ_castSucc (fun i : Fin (p + 2) => (-1 : ℤ) ^ i.val • a i),
    Fin.sum_univ_succ (fun j : Fin (q + 2) => (-1 : ℤ) ^ j.val • b j)]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ,
    pow_zero, one_smul]
  rw [smul_add, Finset.smul_sum]
  simp_rw [smul_smul, ← pow_add]
  have hs : (∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + (j.val + 1)) • b j.succ) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • b j.succ := by
    simp only [Nat.add_assoc, Nat.add_comm 1]
  rw [hs, h, pow_succ]
  simp only [mul_neg_one, neg_smul]
  abel

/-- The Leibniz rule in a common target degree. The interval notation
avoids introducing transports between equal parenthesizations of the degree. -/
theorem differential_cup (p q : ℕ) (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌) :
    differential A (p + q) (cup A x y) =
      A.map (SimplexCategory.subinterval 0 (p + 1) (by omega : 0 + (p + 1) ≤ p + q + 1))
        (differential A p x) *
      A.map (SimplexCategory.subinterval (p + 1) q (by omega : (p + 1) + q ≤ p + q + 1)) y +
      (-1 : ℤ) ^ p •
        (A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q + 1)) x *
        A.map (SimplexCategory.subinterval p (q + 1) (by omega : p + (q + 1) ≤ p + q + 1))
          (differential A q y)) := by
  let a (i : Fin (p + 2)) :=
    A.map (SimplexCategory.subinterval 0 (p + 1) (by omega : 0 + (p + 1) ≤ p + q + 1))
      (A.map (SimplexCategory.δ i) x) *
    A.map (SimplexCategory.subinterval (p + 1) q (by omega : (p + 1) + q ≤ p + q + 1)) y
  let b (i : Fin (q + 2)) :=
    A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q + 1)) x *
    A.map (SimplexCategory.subinterval p (q + 1) (by omega : p + (q + 1) ≤ p + q + 1))
      (A.map (SimplexCategory.δ i) y)
  have hmiddle : a (Fin.last (p + 1)) = b 0 := by
    dsimp only [a, b]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← A.map_comp, ← A.map_comp,
      OAI.AlgebraicTopology.Products.SimplexFaceIdentities.delta_last_comp_frontInterval, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.delta_zero_comp_backInterval]
  have hsum := alternating_cut p q a b hmiddle
  rw [differential, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.sum_face_split p q]
  simp only [OAI.AlgebraicTopology.Products.SimplexFaceIdentities.leftFaceIndex_val, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.rightFaceIndex_val, coface_cup_left, coface_cup_right]
  dsimp only [a, b] at hsum
  convert hsum using 1
  simp only [differential, map_sum, map_zsmul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]

theorem cup_isCocycle {p q : ℕ} (x : A.obj ⦋p⦌) (y : A.obj ⦋q⦌)
    (hx : differential A p x = 0) (hy : differential A q y = 0) :
    differential A (p + q) (cup A x y) = 0 := by
  rw [differential_cup, hx, hy]
  simp only [map_zero, zero_mul, mul_zero, smul_zero, add_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Cup
