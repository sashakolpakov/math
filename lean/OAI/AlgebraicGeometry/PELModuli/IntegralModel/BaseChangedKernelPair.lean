import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedRelations
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base Changed Kernel Pair -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseChangedKernelPair

noncomputable section

section

/-! Actual internal equivalence relations are preserved by base change
in the category of schemes over a base. Joint monicity is proved using
the pullback adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem jointlyMono_overPullback {S S' : Scheme.{0}} (b : S' ⟶ S)
    {R X : Over S} (s t : R ⟶ X) [JointlyMono₂ s t] :
    JointlyMono₂ ((Over.pullback b).map s) ((Over.pullback b).map t) where
  right_cancellation {T} f g hs ht := by
    let adj := Over.mapPullbackAdj b
    apply (adj.homEquiv T R).symm.injective
    apply JointlyMono₂.right_cancellation (p₁ := s) (p₂ := t)
    · have h := congrArg (adj.homEquiv T X).symm hs
      simpa only [adj.homEquiv_naturality_right_symm] using h
    · have h := congrArg (adj.homEquiv T X).symm ht
      simpa only [adj.homEquiv_naturality_right_symm] using h

def overPullback_equivalenceRelation {S S' : Scheme.{0}} (b : S' ⟶ S)
    {R X : Over S} {s t : R ⟶ X} (e : CategoryTheory.EquivalenceRelation s t) :
    CategoryTheory.EquivalenceRelation ((Over.pullback b).map s) ((Over.pullback b).map t) := by
  have : JointlyMono₂ s t := e.toJointlyMono₂
  have : JointlyMono₂ ((Over.pullback b).map s) ((Over.pullback b).map t) :=
    jointlyMono_overPullback b s t
  let hs := e.toSymmetricRelation.map (Over.pullback b)
  let ht := e.toTransitiveRelation.map (Over.pullback b)
  exact {
    toReflexiveRelation := e.toReflexiveRelation.map (Over.pullback b)
    s := hs.s
    symmetry₁ := hs.symmetry₁
    symmetry₂ := hs.symmetry₂
    c := ht.c
    isLimit := ht.isLimit
    t := ht.t
    transitivity₁ := ht.transitivity₁
    transitivity₂ := ht.transitivity₂ }

end

/-! Literal scalar change preserves actual kernel-pair diagrams over a
base, including their underlying scheme diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem over_baseChanged_kernelPair {S S' : Scheme.{0}} (b : S' ⟶ S)
    {W X Y : Over S} (q : X ⟶ Y) (s t : W ⟶ X)
    (h : IsKernelPair q.left s.left t.left) :
    IsKernelPair ((Over.pullback b).map q).left
      ((Over.pullback b).map s).left ((Over.pullback b).map t).left := by
  have hOver : IsKernelPair q s t := h.of_map (Over.forget S) (Over.OverMorphism.ext h.w)
  exact (hOver.map (Over.pullback b)).map (Over.forget S')

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseChangedKernelPair
