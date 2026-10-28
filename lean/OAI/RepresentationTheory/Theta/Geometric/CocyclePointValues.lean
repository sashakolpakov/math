import OAI.RepresentationTheory.Theta.Geometric.ContinuousLine
import OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms

/-! # Cocycle Point Values -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Compact normal spaces supply logarithms of actual nonvanishing
transition cocycles and their rational singular Chern classes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms.Construction

variable {T : TopCat} {I : Type} (C : ContinuousLine.ContinuousLineCocycle T I)

def ContinuousLine.ContinuousLineCocycle.transitionPair (i j : I) : C((C.cover i ⊓ C.cover j : Opens T), ℂ) :=
  (C.transition ![i,j]).comp (AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms.Construction.pair_le_cechIntersection C.cover ![i,j]))

theorem ContinuousLine.ContinuousLineCocycle.transitionPair_nonzero (i j : I) (p : (C.cover i ⊓ C.cover j : Opens T)) :
    C.transitionPair i j p ≠ 0 := C.nonzero _ _

theorem ContinuousLine.ContinuousLineCocycle.transition_congr {a b : Fin 2 → I} (hab : a = b)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection C.cover a) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection C.cover b) (hpq : p.val = q.val) :
    C.transition a p = C.transition b q := by
  subst b
  exact congrArg (C.transition a) (Subtype.ext hpq)

variable [CompactSpace T] [NormalSpace T]

def ContinuousLine.ContinuousLineCocycle.logRefinement : AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen.Construction.CompactLogarithmicRefinement C.cover C.transitionPair :=
  Classical.choice (AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen.Construction.nonempty_compactLogarithmicRefinement C.cover C.covers C.transitionPair C.transitionPair_nonzero)

abbrev ContinuousLine.ContinuousLineCocycle.LogIndex := T × C.logRefinement.charts
abbrev ContinuousLine.ContinuousLineCocycle.logCover : C.LogIndex → Opens T := C.logRefinement.refinement.cover
abbrev ContinuousLine.ContinuousLineCocycle.logParent (a : C.LogIndex) : I := a.2.val

theorem ContinuousLine.ContinuousLineCocycle.logCover_subset (a : C.LogIndex) : C.logCover a ≤ C.cover (C.logParent a) :=
  C.logRefinement.refinement.subset a

theorem ContinuousLine.ContinuousLineCocycle.logCover_covers (p : T) : ∃ a, p ∈ C.logCover a :=
  C.logRefinement.refinement.covers p

def ContinuousLine.ContinuousLineCocycle.logarithm : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.LogCechCochain T C.logCover :=
  fun a => (C.logRefinement.refinement.logarithm (a 0) (a 1)).comp
    (AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms.Construction.cechIntersection_le_pair C.logCover a))

theorem ContinuousLine.ContinuousLineCocycle.logIntersection_subset {n : ℕ} (a : Fin (n + 1) → C.LogIndex) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection C.logCover a ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection C.cover (C.logParent ∘ a) := by
  intro p hp
  apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection C.cover (C.logParent ∘ a) p).mpr
  intro k
  exact C.logCover_subset (a k) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le C.logCover a k hp)

theorem ContinuousLine.ContinuousLineCocycle.exp_logarithm (a : Fin 2 → C.LogIndex) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection C.logCover a) :
    Complex.exp (C.logarithm a p) =
      C.transition (C.logParent ∘ a) ⟨p.val, C.logIntersection_subset a p.property⟩ := by
  have h := C.logRefinement.refinement.exp_logarithm (a 0) (a 1)
    (AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms.Construction.cechIntersection_le_pair C.logCover a) p)
  have ha : ![C.logParent (a 0), C.logParent (a 1)] = C.logParent ∘ a := by
    funext k
    fin_cases k <;> rfl
  change Complex.exp (C.logarithm a p) = C.transition ![C.logParent (a 0), C.logParent (a 1)] _ at h
  exact h.trans (C.transition_congr ha _ _ rfl)

theorem ContinuousLine.ContinuousLineCocycle.logarithm_cocycle : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle T C.logCover C.logarithm := by
  intro a p
  change Complex.exp (C.logarithm (a ∘ (2 : Fin 3).succAbove) _) *
    Complex.exp (C.logarithm (a ∘ (0 : Fin 3).succAbove) _) =
      Complex.exp (C.logarithm (a ∘ (1 : Fin 3).succAbove) _)
  rw [ContinuousLine.ContinuousLineCocycle.exp_logarithm, ContinuousLine.ContinuousLineCocycle.exp_logarithm, ContinuousLine.ContinuousLineCocycle.exp_logarithm]
  exact C.cocycle (C.logParent ∘ a) ⟨p.val, C.logIntersection_subset a p.property⟩

def ContinuousLine.ContinuousLineCocycle.chernClass : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) T 2 :=
  AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T C.logCover C.logCover_covers C.logarithm C.logarithm_cocycle

end

/-! Pointwise change-of-frame identities follow from the actual
nonvanishing transition cocycle. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace

variable {T : TopCat} {I : Type} (C : ContinuousLine.ContinuousLineCocycle T I)

abbrev ContinuousLine.ContinuousLineCocycle.pointTransition (i j : I) (p : T) (hi : p ∈ C.cover i) (hj : p ∈ C.cover j) : ℂ :=
  C.transitionPair i j ⟨p, hi, hj⟩

theorem ContinuousLine.ContinuousLineCocycle.transition_eq_point (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection C.cover a) :
    C.transition a p = C.pointTransition (a 0) (a 1) p.val
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le C.cover a 0 p.property) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le C.cover a 1 p.property) := by
  apply C.transition_congr (show a = ![a 0, a 1] by funext k; fin_cases k <;> rfl) _ _ rfl

theorem ContinuousLine.ContinuousLineCocycle.pointTransition_cocycle (i j k : I) (p : T)
    (hi : p ∈ C.cover i) (hj : p ∈ C.cover j) (hk : p ∈ C.cover k) :
    C.pointTransition i j p hi hj * C.pointTransition j k p hj hk = C.pointTransition i k p hi hk := by
  have hp : p ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection C.cover ![i,j,k] := by
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection C.cover ![i,j,k] p).mpr
    intro a
    fin_cases a
    · exact hi
    · exact hj
    · exact hk
  have h := C.cocycle ![i,j,k] ⟨p, hp⟩
  rw [ContinuousLine.ContinuousLineCocycle.transition_eq_point, ContinuousLine.ContinuousLineCocycle.transition_eq_point, ContinuousLine.ContinuousLineCocycle.transition_eq_point] at h
  exact h

theorem ContinuousLine.ContinuousLineCocycle.pointTransition_gauge (i j k l : I) (p : T)
    (hi : p ∈ C.cover i) (hj : p ∈ C.cover j) (hk : p ∈ C.cover k) (hl : p ∈ C.cover l) :
    C.pointTransition k l p hk hl =
      C.pointTransition i j p hi hj * C.pointTransition j l p hj hl / C.pointTransition i k p hi hk := by
  apply (eq_div_iff (C.transitionPair_nonzero i k ⟨p, hi, hk⟩)).mpr
  rw [mul_comm, ContinuousLine.ContinuousLineCocycle.pointTransition_cocycle, ContinuousLine.ContinuousLineCocycle.pointTransition_cocycle]

end

end OAI.RepresentationTheory.Theta.Geometric
