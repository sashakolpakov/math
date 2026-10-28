import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.Cup
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Bilinear Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.BilinearCup

noncomputable section

/-! The Alexander–Whitney formula for a natural bilinear pairing of
cosimplicial modules. This also applies to pairings between different
degrees of a cosimplicial differential graded algebra. -/

open _root_.CategoryTheory
open scoped Simplicial

universe u v

variable {R : Type u} [CommRing R]
  (A B C : CosimplicialObject (ModuleCat.{v} R))

def complex : CochainComplex (ModuleCat.{v} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).obj A

def differential (n : ℕ) : A.obj ⦋n⦌ →ₗ[R] A.obj ⦋n + 1⦌ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (A.map (SimplexCategory.δ i)).hom

theorem differential_apply (n : ℕ) (x : A.obj ⦋n⦌) :
    differential A n x = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • A.map (SimplexCategory.δ i) x := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply]

theorem complex_d_apply (n : ℕ) (x : A.obj ⦋n⦌) :
    (complex A).d n (n + 1) x = differential A n x := by
  dsimp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  change (AlgebraicTopology.AlternatingCofaceMapComplex.objD A n).hom x = _
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, differential]
  rfl

variable (μ : ∀ n : SimplexCategory, A.obj n →ₗ[R] B.obj n →ₗ[R] C.obj n)
  (hμ : ∀ {m n : SimplexCategory} (f : m ⟶ n) (x : A.obj m) (y : B.obj m),
    C.map f (μ m x y) = μ n (A.map f x) (B.map f y))

def cup (p q : ℕ) : A.obj ⦋p⦌ →ₗ[R] B.obj ⦋q⦌ →ₗ[R] C.obj ⦋p + q⦌ :=
  (μ ⦋p + q⦌).compl₁₂ (A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q)).hom (B.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q)).hom

theorem cup_apply (p q : ℕ) (x : A.obj ⦋p⦌) (y : B.obj ⦋q⦌) :
    cup A B C μ p q x y = μ ⦋p + q⦌ (A.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion p q) x)
      (B.map (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q) y) := rfl

include hμ in
theorem coface_cup_left (p q : ℕ) (x : A.obj ⦋p⦌) (y : B.obj ⦋q⦌)
    (i : Fin (p + 1)) :
    C.map (SimplexCategory.δ (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.leftFaceIndex p q i)) (cup A B C μ p q x y) =
      μ ⦋p + q + 1⦌
        (A.map (SimplexCategory.subinterval 0 (p + 1) (by omega : 0 + (p + 1) ≤ p + q + 1))
          (A.map (SimplexCategory.δ i.castSucc) x))
        (B.map (SimplexCategory.subinterval (p + 1) q (by omega : (p + 1) + q ≤ p + q + 1)) y) := by
  rw [cup_apply, hμ]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← A.map_comp, ← A.map_comp, ← B.map_comp,
    OAI.AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion_comp_delta_left, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion_comp_delta_left]

include hμ in
theorem coface_cup_right (p q : ℕ) (x : A.obj ⦋p⦌) (y : B.obj ⦋q⦌)
    (i : Fin (q + 1)) :
    C.map (SimplexCategory.δ (OAI.AlgebraicTopology.Products.SimplexFaceIdentities.rightFaceIndex p q i)) (cup A B C μ p q x y) =
      μ ⦋p + q + 1⦌
        (A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q + 1)) x)
        (B.map (SimplexCategory.subinterval p (q + 1) (by omega : p + (q + 1) ≤ p + q + 1))
          (B.map (SimplexCategory.δ i.succ) y)) := by
  rw [cup_apply, hμ]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← A.map_comp, ← B.map_comp, ← B.map_comp,
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

include hμ in
theorem differential_cup (p q : ℕ) (x : A.obj ⦋p⦌) (y : B.obj ⦋q⦌) :
    differential C (p + q) (cup A B C μ p q x y) =
      μ ⦋p + q + 1⦌
        (A.map (SimplexCategory.subinterval 0 (p + 1) (by omega : 0 + (p + 1) ≤ p + q + 1))
          (differential A p x))
        (B.map (SimplexCategory.subinterval (p + 1) q (by omega : (p + 1) + q ≤ p + q + 1)) y) +
      (-1 : ℤ) ^ p • μ ⦋p + q + 1⦌
        (A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q + 1)) x)
        (B.map (SimplexCategory.subinterval p (q + 1) (by omega : p + (q + 1) ≤ p + q + 1))
          (differential B q y)) := by
  let a (i : Fin (p + 2)) := μ ⦋p + q + 1⦌
    (A.map (SimplexCategory.subinterval 0 (p + 1) (by omega : 0 + (p + 1) ≤ p + q + 1))
      (A.map (SimplexCategory.δ i) x))
    (B.map (SimplexCategory.subinterval (p + 1) q (by omega : (p + 1) + q ≤ p + q + 1)) y)
  let b (i : Fin (q + 2)) := μ ⦋p + q + 1⦌
    (A.map (SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q + 1)) x)
    (B.map (SimplexCategory.subinterval p (q + 1) (by omega : p + (q + 1) ≤ p + q + 1))
      (B.map (SimplexCategory.δ i) y))
  have hmiddle : a (Fin.last (p + 1)) = b 0 := by
    dsimp only [a, b]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← A.map_comp, ← B.map_comp, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.delta_last_comp_frontInterval, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.delta_zero_comp_backInterval]
  have hsum := alternating_cut p q a b hmiddle
  rw [differential_apply, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.sum_face_split p q]
  simp only [OAI.AlgebraicTopology.Products.SimplexFaceIdentities.leftFaceIndex_val, OAI.AlgebraicTopology.Products.SimplexFaceIdentities.rightFaceIndex_val, coface_cup_left A B C μ hμ,
    coface_cup_right A B C μ hμ]
  dsimp only [a, b] at hsum
  convert hsum using 1
  simp only [differential_apply, map_sum, map_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.BilinearCup
