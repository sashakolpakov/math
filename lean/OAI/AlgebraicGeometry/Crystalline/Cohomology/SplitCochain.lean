import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Homotopy

/-! # Split Cochain -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SplitCochain.SplitCochainContraction

noncomputable section

/-!
# A split two-term cochain complex contracts onto its constants

This categorical lemma packages an explicit primitive and constant
projection as a homotopy equivalence. Its inputs are the splitting
identities, not an assumed quasi-isomorphism.
-/

open _root_.CategoryTheory Limits _root_.HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V]
  (K : CochainComplex V ℕ) (A : V)
  (c : A ⟶ K.X 0) (r : K.X 0 ⟶ A) (s : K.X 1 ⟶ K.X 0)
  (hc : c ≫ K.d 0 1 = 0) (hr : c ≫ r = 𝟙 A)
  (h0 : K.d 0 1 ≫ s + r ≫ c = 𝟙 (K.X 0))
  (h1 : s ≫ K.d 0 1 = 𝟙 (K.X 1))
  (higher : ∀ n : ℕ, 2 ≤ n → IsZero (K.X n))

def augmentation : (CochainComplex.single₀ V).obj A ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K A).symm ⟨c, hc⟩

def projection : K ⟶ (CochainComplex.single₀ V).obj A :=
  (CochainComplex.toSingle₀Equiv K A).symm r

@[simp] theorem augmentation_zero : (augmentation K A c hc).f 0 = c :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero c hc

@[simp] theorem projection_zero : (projection K A r).f 0 = r :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_zero r

@[simp] theorem projection_succ (n : ℕ) : (projection K A r).f (n + 1) = 0 :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_succ r n

include hr in
theorem augmentation_projection : augmentation K A c hc ≫ projection K A r = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  change (augmentation K A c hc).f 0 ≫ (projection K A r).f 0 = 𝟙 _
  rw [augmentation_zero, projection_zero]
  exact hr

def contractingHom : ∀ i j : ℕ, K.X i ⟶ K.X j
  | 1, 0 => s
  | _, _ => 0

/-- The explicit primitive is a homotopy from the identity to the constant projection. -/
def contraction : Homotopy (𝟙 K) (projection K A r ≫ augmentation K A c hc) where
  hom := contractingHom K s
  zero i j hij := by
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero =>
        cases j with
        | zero => exact (hij rfl).elim
        | succ j => rfl
      | succ i => rfl
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl), prevD_nat]
      change 𝟙 (K.X 0) = K.d 0 1 ≫ s + 0 ≫ K.d 0 0 +
        (projection K A r).f 0 ≫ (augmentation K A c hc).f 0
      rw [zero_comp, add_zero, projection_zero, augmentation_zero]
      exact h0.symm
    | succ i =>
      cases i with
      | zero =>
        rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel 1 2 from rfl), prevD_nat]
        change 𝟙 (K.X 1) = K.d 1 2 ≫ 0 + s ≫ K.d 0 1 +
          (projection K A r).f 1 ≫ (augmentation K A c hc).f 1
        simp only [projection_succ, comp_zero, zero_add, zero_comp, add_zero]
        exact h1.symm
      | succ i => exact (higher (i + 2) (by omega)).eq_of_src _ _

/-- A concrete cochain homotopy equivalence supplied by the split local calculation. -/
def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ V).obj A) K where
  hom := augmentation K A c hc
  inv := projection K A r
  homotopyHomInvId := Homotopy.ofEq (augmentation_projection K A c r hc hr)
  homotopyInvHomId := (contraction K A c r s hc h0 h1 higher).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SplitCochain.SplitCochainContraction
