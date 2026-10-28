import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Homotopy

/-! # Single Retraction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleRetraction.SingleRetractionHomotopy

noncomputable section

/-!
# Retraction onto a single cochain degree

A chain map homotopic to the identity, zero in positive degree, and
explicitly split in degree zero gives a homotopy equivalence with its constants.
-/

open _root_.CategoryTheory Limits _root_.HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] [Limits.HasZeroObject V]
  (K : CochainComplex V ℕ) (A : V) (q : K ⟶ K) (h : Homotopy (𝟙 K) q)
  (c : A ⟶ K.X 0) (r : K.X 0 ⟶ A)
  (hc : c ≫ K.d 0 1 = 0) (hr : c ≫ r = 𝟙 A)
  (h0 : r ≫ c = q.f 0) (hpos : ∀ n, q.f (n + 1) = 0)

def augmentation : (CochainComplex.single₀ V).obj A ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K A).symm ⟨c, hc⟩

def projection : K ⟶ (CochainComplex.single₀ V).obj A :=
  (CochainComplex.toSingle₀Equiv K A).symm r

theorem augmentation_zero : (augmentation K A c hc).f 0 = c :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero c hc

theorem projection_zero : (projection K A r).f 0 = r :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_zero r

theorem projection_succ (n : ℕ) : (projection K A r).f (n + 1) = 0 :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_succ r n

include hr in
theorem augmentation_projection : augmentation K A c hc ≫ projection K A r = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  change (augmentation K A c hc).f 0 ≫ (projection K A r).f 0 = 𝟙 _
  rw [augmentation_zero, projection_zero]
  exact hr

include h0 hpos in
theorem projection_augmentation : projection K A r ≫ augmentation K A c hc = q := by
  ext n : 1
  cases n with
  | zero =>
    change (projection K A r).f 0 ≫ (augmentation K A c hc).f 0 = q.f 0
    rw [projection_zero, augmentation_zero]
    exact h0
  | succ n =>
    change (projection K A r).f (n + 1) ≫ (augmentation K A c hc).f (n + 1) = q.f (n + 1)
    rw [projection_succ, zero_comp, hpos]

def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ V).obj A) K where
  hom := augmentation K A c hc
  inv := projection K A r
  homotopyHomInvId := Homotopy.ofEq (augmentation_projection K A c r hc hr)
  homotopyInvHomId := (Homotopy.ofEq (projection_augmentation K A q c r hc h0 hpos)).trans h.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleRetraction.SingleRetractionHomotopy
