import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatRegularQuotientRing

/-! # Witt Tuple Scalar Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleScalarKernel

noncomputable section

/-! Multiplication by p on every native Witt tuple ring has exactly the expected kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem scalar_kernel (n a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X)
    (x : (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t).obj.ring) :
    (p : ℕ) • x = 0 ↔ ∃ y, (p ^ n : ℕ) • y = x := by
  let U := Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t
  let f := BoundedCrystalline.BaseRing.base (Witt.Crystalline.wittStructureMap p k X) n U
  have hs : f (RegularQuotientScalarExactness.scalar (WittVector p k) (p : WittVector p k) n) =
      (p : U.obj.ring) := map_natCast U.obj.base p
  have hr : IsSMulRegular (WittVector p k) (p : WittVector p k) :=
    (IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)).left
  have h := FlatRegularQuotientRing.exact (WittVector p k) (p : WittVector p k) hr n U.obj.ring f
    (WittTupleFlatness.tuple_flat p k X n a t) x
  rw [hs] at h
  simpa only [nsmul_eq_mul, Nat.cast_pow] using h

theorem quotient_kernel (n m : ℕ) (hnm : n ≤ m) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X)
    (x : (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t).obj.ring) :
    (WittTupleReduction.morphism p k X n m hnm a t).ringMap x = 0 ↔
      ∃ y, (p ^ (n + 1) : ℕ) • y = x := by
  have h : (WittTupleReduction.morphism p k X n m hnm a t).ringMap x = 0 ↔
      x ∈ (Ideal.span {(p : (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t).obj.ring)}) ^ (n + 1) := by
    change x ∈ RingHom.ker (WittTupleReduction.morphism p k X n m hnm a t).ringMap.toRingHom ↔ _
    rw [WittTupleReduction.kernel]
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := h.mp hx
    exact ⟨y, by simpa only [nsmul_eq_mul, Nat.cast_pow] using hy.symm⟩
  · rintro ⟨y, hy⟩
    apply h.mpr
    exact ⟨y, by simpa only [nsmul_eq_mul, Nat.cast_pow] using hy.symm⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleScalarKernel
