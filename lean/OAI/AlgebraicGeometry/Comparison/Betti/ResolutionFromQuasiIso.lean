import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage

/-! # Resolution From Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ResolutionFromQuasiIso

noncomputable section

/-! A proved quasi-isomorphic augmentation gives actual kernel and
positive exactness data for its nonnegative resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {Z : C} {K : CochainComplex C ℕ}
  (α : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso α]

omit [QuasiIso α] in
theorem augmentation_zero_comp : α.f 0 ≫ K.d 0 1 = 0 := by
  rw [α.comm]
  exact zero_comp

def augmentation_kernel : IsLimit (KernelFork.ofι (α.f 0) (augmentation_zero_comp α)) := by
  let S := K.sc' 0 0 1
  have hq : QuasiIsoAt α 0 := inferInstance
  have hq' := (CochainComplex.quasiIsoAt₀_iff α).mp hq
  have hi : IsIso (S.liftCycles (α.f 0) (augmentation_zero_comp α)) :=
    (ShortComplex.quasiIso_iff_isIso_liftCycles
      ((shortComplexFunctor' C (.up ℕ) 0 0 1).map α)
      (by rfl) (by rfl) (K.shape 0 0 (by decide))).mp hq'
  let e := asIso (S.liftCycles (α.f 0) (augmentation_zero_comp α))
  refine IsLimit.ofIsoLimit S.cyclesIsKernel (Fork.ext e.symm ?_)
  apply (cancel_epi e.hom).mp
  change e.hom ≫ e.inv ≫ α.f 0 = e.hom ≫ S.iCycles
  rw [e.hom_inv_id_assoc]
  exact (S.liftCycles_i (α.f 0) (augmentation_zero_comp α)).symm

def ofQuasiIsoAugmentation : ResolutionExactImage.Data Z where
  complex := K
  augmentation := α.f 0
  augmentation_d := augmentation_zero_comp α
  isKernel := augmentation_kernel α
  exact_succ n := (quasiIsoAt_iff_exactAt α (n + 1)
    (exactAt_single_obj (.up ℕ) 0 Z (n + 1) (Nat.succ_ne_zero n))).mp inferInstance

theorem ofQuasiIsoAugmentation_cochain : ResolutionExactImage.cochainAugmentation (ofQuasiIsoAugmentation α) = α := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      dsimp only [ResolutionExactImage.cochainAugmentation, ofQuasiIsoAugmentation]
      exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
  | succ n => exact (isZero_single_obj_X (.up ℕ) 0 Z (n + 1) (Nat.succ_ne_zero n)).eq_of_src _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.ResolutionFromQuasiIso
