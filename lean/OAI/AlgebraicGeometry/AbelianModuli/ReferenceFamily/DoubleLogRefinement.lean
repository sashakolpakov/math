import OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen

/-! # Double Log Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DoubleLogRefinement

noncomputable section

/-! A single refinement carries logarithms of two families of continuous
nonvanishing transitions, with the same original parent chart at each
refined chart. This permits tensor addition without changing frames. -/

open _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen.Construction

variable {T I : Type} [TopologicalSpace T]

structure DoubleLogarithmicRefinement (U : I → Opens T)
    (g h : ∀ i j, C((U i ⊓ U j : Opens T), ℂ)) where
  Index : Type
  cover : Index → Opens T
  parent : Index → I
  subset : ∀ i, cover i ≤ U (parent i)
  covers : ∀ x, ∃ i, x ∈ cover i
  leftLog : ∀ i j, C((cover i ⊓ cover j : Opens T), ℂ)
  rightLog : ∀ i j, C((cover i ⊓ cover j : Opens T), ℂ)
  left_exp : ∀ i j (x : (cover i ⊓ cover j : Opens T)),
    Complex.exp (leftLog i j x) = g (parent i) (parent j) ⟨x.val, subset i x.property.1, subset j x.property.2⟩
  right_exp : ∀ i j (x : (cover i ⊓ cover j : Opens T)),
    Complex.exp (rightLog i j x) = h (parent i) (parent j) ⟨x.val, subset i x.property.1, subset j x.property.2⟩

theorem nonempty_doubleLogarithmicRefinement [CompactSpace T] [NormalSpace T]
    (U : I → Opens T) (hU : ∀ x, ∃ i, x ∈ U i)
    (g h : ∀ i j, C((U i ⊓ U j : Opens T), ℂ))
    (hg : ∀ i j x, g i j x ≠ 0) (hh : ∀ i j x, h i j x ≠ 0) :
    Nonempty (DoubleLogarithmicRefinement U g h) := by
  let A := Classical.choice (DivisorClass.Chern.LogRefinementOpen.Construction.nonempty_compactLogarithmicRefinement U hU g hg)
  let J := T × A.charts
  let V : J → Opens T := A.refinement.cover
  let p (i : J) : I := i.2.val
  let k (i j : J) : C((V i ⊓ V j : Opens T), ℂ) :=
    (h (p i) (p j)).comp (DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap
      (le_inf (inf_le_left.trans (A.refinement.subset i))
        (inf_le_right.trans (A.refinement.subset j))))
  have hk : ∀ i j x, k i j x ≠ 0 := fun i j x => hh (p i) (p j) _
  let B := Classical.choice (DivisorClass.Chern.LogRefinementOpen.Construction.nonempty_compactLogarithmicRefinement V A.refinement.covers k hk)
  let K := T × B.charts
  let r (i : K) : J := i.2.val
  refine ⟨{
    Index := K
    cover := B.refinement.cover
    parent := fun i => p (r i)
    subset := fun i => (B.refinement.subset i).trans (A.refinement.subset (r i))
    covers := B.refinement.covers
    leftLog := fun i j => (A.refinement.logarithm (r i) (r j)).comp
      (DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (le_inf (inf_le_left.trans (B.refinement.subset i))
        (inf_le_right.trans (B.refinement.subset j))))
    rightLog := B.refinement.logarithm
    left_exp := ?_
    right_exp := ?_ }⟩
  · intro i j x
    exact A.refinement.exp_logarithm (r i) (r j)
      ⟨x.val, B.refinement.subset i x.property.1, B.refinement.subset j x.property.2⟩
  · intro i j x
    exact B.refinement.exp_logarithm i j x

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DoubleLogRefinement
