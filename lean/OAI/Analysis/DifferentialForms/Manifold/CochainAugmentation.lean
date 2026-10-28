import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-! # Cochain Augmentation -/

namespace OAI.Analysis.DifferentialForms.Manifold.CochainAugmentation

noncomputable section

section

/-!
# Homological algebra for an actual cochain augmentation

The general lemmas here are applied to the proved de Rham kernel and local
exactness theorems in `DeRhamResolution`. They do not supply those analytic
hypotheses themselves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- Beyond the inserted two initial terms, augmentation only shifts exactness. -/
theorem cochainAugment_exactAt_succ_succ (K : CochainComplex C ℕ) {X : C}
    (f : X ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0) (n : ℕ) :
    (K.augment f hf).ExactAt (n + 2) ↔ K.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp),
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  rfl

/-- A known kernel object maps isomorphically to the categorical cycles. -/
theorem shortComplex_liftCycles_isIso_of_kernel (S : ShortComplex C) [S.HasHomology]
    {X : C} (f : X ⟶ S.X₂) (hf : f ≫ S.g = 0)
    (hkernel : IsLimit (KernelFork.ofι f hf)) : IsIso (S.liftCycles f hf) := by
  have heq : S.liftCycles f hf = (S.isoCyclesOfIsLimit hkernel).hom := by
    apply (cancel_mono S.iCycles).1
    rw [S.liftCycles_i, S.isoCyclesOfIsLimit_hom_iCycles]
    rfl
  rw [heq]
  infer_instance

variable [HasZeroObject C] [CategoryWithHomology C]

/-- A kernel inclusion into degree zero is a quasi-isomorphism precisely when
the positive terms are exact; this direction packages those proved inputs. -/
theorem cochainAugmentation_quasiIso (K : CochainComplex C ℕ) {X : C}
    (f : X ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0)
    (hkernel : IsLimit (KernelFork.ofι f hf))
    (hexact : ∀ n : ℕ, K.ExactAt (n + 1)) :
    QuasiIso ((CochainComplex.fromSingle₀Equiv K X).symm ⟨f, hf⟩) := by
  let α := (CochainComplex.fromSingle₀Equiv K X).symm ⟨f, hf⟩
  change QuasiIso α
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    apply (ShortComplex.quasiIso_iff_isIso_liftCycles
      ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 0 0 1).map α)
      (by rfl) (by rfl) (by
        change K.d 0 0 = 0
        exact K.shape 0 0 (by simp))).2
    change IsIso ((K.sc' 0 0 1).liftCycles (α.f 0) _)
    simpa only [α, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
      CochainComplex.single₀_obj_zero] using
      (shortComplex_liftCycles_isIso_of_kernel (K.sc' 0 0 1) f hf hkernel)
  | succ n =>
    exact (quasiIsoAt_iff_exactAt α (n + 1)
      (HomologicalComplex.exactAt_single_obj (ComplexShape.up ℕ) 0 X (n + 1)
        (Nat.succ_ne_zero n))).2 (hexact n)

end

/-! Exactness of a cochain augmentation from its genuine kernel and positive exactness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  [CategoryWithHomology C]

/-- A genuine kernel inclusion followed by an exact positive complex gives an
acyclic augmented complex. -/
theorem cochainAugment_acyclic_of_kernel (K : CochainComplex C ℕ) {X : C}
    (f : X ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0)
    (hkernel : IsLimit (KernelFork.ofι f hf))
    (hexact : ∀ n : ℕ, K.ExactAt (n + 1)) :
    (K.augment f hf).Acyclic := by
  intro i
  cases i with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)]
    change (ShortComplex.mk (0 : X ⟶ X) f (zero_comp)).Exact
    exact (ShortComplex.exact_iff_mono _ rfl).2 (mono_of_isLimit_fork hkernel)
  | succ i =>
    cases i with
    | zero =>
      rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
      change (ShortComplex.mk f (K.d 0 1) hf).Exact
      exact ShortComplex.exact_of_f_is_kernel _ hkernel
    | succ n =>
      exact (cochainAugment_exactAt_succ_succ K f hf n).2 (hexact n)

end

end OAI.Analysis.DifferentialForms.Manifold.CochainAugmentation
