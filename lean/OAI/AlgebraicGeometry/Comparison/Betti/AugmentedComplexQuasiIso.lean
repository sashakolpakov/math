import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # Augmented Complex Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AugmentedComplexQuasiIso.Ext

noncomputable section

/-! An exact augmented nonnegative complex resolves its actual augmentation object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {A : C}
  (K : CochainComplex C ℕ) (e : A ⟶ K.X 0) (w : e ≫ K.d 0 1 = 0)

def nonnegativeAugmentation : (CochainComplex.single₀ C).obj A ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K A).symm ⟨e, w⟩

theorem nonnegativeAugmentation_quasiIso [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, K.ExactAt (n + 1)) : QuasiIso (nonnegativeAugmentation K e w) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp; rfl) (by simp; rfl) (by simp; rfl)]
    change (ShortComplex.mk ((nonnegativeAugmentation K e w).f 0) (K.d 0 1) _).Exact ∧
      Mono ((nonnegativeAugmentation K e w).f 0)
    simpa only [nonnegativeAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
      CochainComplex.single₀_obj_zero]
      using And.intro haug (inferInstance : Mono e)
  | succ n =>
    exact (quasiIsoAt_iff_exactAt (nonnegativeAugmentation K e w) (n + 1)
      (CochainComplex.exactAt_succ_single_obj A n)).mpr (hpos n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.AugmentedComplexQuasiIso.Ext
