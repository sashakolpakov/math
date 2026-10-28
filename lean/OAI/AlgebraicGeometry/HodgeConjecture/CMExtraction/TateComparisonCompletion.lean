import OAI.RepresentationTheory.Theta.Geometric.TateComparison
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseExt

/-! # Tate Comparison Completion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic

noncomputable section

/-! Recover the full TateComparison conclusions for any native GeometricTheta action realizing
the same geometry. Point push uniquely determines its integral operators;
the graph and raw-kernel conditions determine its shift and basis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseExt.Construction OAI.RepresentationTheory.Theta.Geometric.TateComparison

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)

theorem albanese_end_ext_of_differences (a b : D.EndK)
    (hab : ∀ (k : Type) [Field k] [IsAlgClosed k] (c : Spec (.of k) ⟶ Spec (.of K))
      (j : Fin D.componentCount) (x y : Over.mk c ⟶ D.componentGeneric j),
      D.endPoint a (D.aPoint hg j x - D.aPoint hg j y) =
        D.endPoint b (D.aPoint hg j x - D.aPoint hg j y)) : a = b := by
  have h : a - b + 1 = 1 := by
    apply AbelianScheme.CentralAction.AlbaneseExt.Construction.albanese_end_eq_one_of_differences D hg
    intro k _ _ c j x y
    have he := hab k c j x y
    simp only [AbelianScheme.CentralAction.AlbaneseExt.Construction.endPoint_eq_app] at he ⊢
    let z : (AbelianScheme.TateComparison.End.additivePoints D.albaneseGroup.X).obj (.op (Over.mk c)) :=
      D.aPoint hg j x - D.aPoint hg j y
    change (a.app (.op (Over.mk c))).hom z - (b.app (.op (Over.mk c))).hom z + z = z
    rw [he, sub_self, zero_add]
  exact sub_eq_zero.mp (add_right_cancel (h.trans (zero_add (1 : D.EndK)).symm))

theorem native_integral_action_unique (A B : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hA : A.IsRealization D hg hq hIsogenyQuotient) (hB : B.IsRealization D hg hq hIsogenyQuotient) :
    A.integral = B.integral := by
  funext t
  apply albanese_end_ext_of_differences D hg
  intro k _ _ c j x y
  exact (hA.pointPush t k c j x y).trans (hB.pointPush t k c j x y).symm

theorem native_shift_unique (A B : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hA : A.IsRealization D hg hq hIsogenyQuotient) (hB : B.IsRealization D hg hq hIsogenyQuotient) :
    A.shift = B.shift := by
  obtain ⟨eA, heA, htA⟩ := hA.graph
  obtain ⟨eB, heB, htB⟩ := hB.graph
  apply Iso.ext
  apply (cancel_epi eA.hom).mp
  exact htA.symm.trans (htB.trans (by rw [heA, heB]))

/-- This projection retains exactly the given native operators. -/
def fullNativeAction (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (coeff : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ) : AbelianScheme.CentralAction.Interface.Construction.ActionData D :=
  ⟨A.basis, coeff, A.shift, A.integral, A.algebraAction, A.cohomologyAction⟩

theorem native_action_full_conclusion (h : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D hg hq hIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (hA : A.IsRealization D hg hq hIsogenyQuotient) :
    ∃ coeff, AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient (fullNativeAction D A coeff) := by
  obtain ⟨hflags, basis, coeff, shift, hbasis, hcoeff, hneighbors, hcentral, hgraph,
    hscalarNeighbors, hclears, integral, rho, rhoH1, hint, hpush, hintMul, hunit, hH1,
    hforms⟩ := h
  let B : RepresentationTheory.Theta.Geometric.TateComparison.Action D := ⟨basis, shift, integral, rho, rhoH1⟩
  have hB : B.IsRealization D hg hq hIsogenyQuotient :=
    ⟨hflags, hbasis, hcentral, hgraph, hint, hunit, hpush, hH1, hforms⟩
  have hb : A.basis = basis := by
    funext t
    exact AbelianScheme.TateComparison.HeckeKernel.rawDoubleCoset_unique (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (hA.basis t) (hbasis t)
  have hi : A.integral = integral := native_integral_action_unique D hg hq hIsogenyQuotient A B hA hB
  have hs : A.shift = shift := native_shift_unique D hg hq hIsogenyQuotient A B hA hB
  refine ⟨coeff, hA.flags, hA.basis, ?_, hneighbors, hA.central, hA.graph, ?_, ?_,
    hA.integral, hA.pointPush, ?_, hA.centralUnit, hA.cohomology, hA.forms⟩
  · simpa only [fullNativeAction, hb] using hcoeff
  · simpa only [fullNativeAction, hs] using hscalarNeighbors
  · simpa only [fullNativeAction, hb] using hclears
  · simpa only [fullNativeAction, hi] using hintMul

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic
