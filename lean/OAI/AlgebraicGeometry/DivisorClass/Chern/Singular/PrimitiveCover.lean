import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Refinement
import OAI.AlgebraicTopology.Cohomology.Singular.LocalPrimitives

/-! # Primitive Cover -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.PrimitiveCover

noncomputable section

/-! Actual local primitives of a global singular degree-two cocycle. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.LocalPrimitives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0})

structure SingularTwoPrimitiveCover (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2) where
  cover : X → Opens X
  mem_cover : ∀ x, x ∈ cover x
  primitive : ∀ i, (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (cover i))).X 1
  differential : ∀ i,
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (cover i))).d 1 2 (primitive i) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (Opens.inclusion' (cover i))).f 2 c.val

theorem nonempty_singularTwoPrimitiveCover [StronglyLocallyContractibleSpace X]
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2) : Nonempty (SingularTwoPrimitiveCover X c) := by
  let A := ModuleCat.of ℚ ℚ
  let cTop := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A (Opens.inclusion' (⊤ : Opens X))) 2 c
  have h : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      ∃ b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A (TopCat.of V)).X 1,
        (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A (TopCat.of V)).d 1 2 b =
          (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A (Opens.inclusion' V)).f 2 c.val := by
    intro x
    obtain ⟨V, hx, hV, b, hb⟩ := AlgebraicTopology.Cohomology.Singular.LocalPrimitives.exists_local_singularPrimitive A X ⊤ x (by trivial) 1 cTop
    refine ⟨V, hx, b, ?_⟩
    have he : (Opens.toTopCat X).map (homOfLE hV) ≫ Opens.inclusion' (⊤ : Opens X) =
        Opens.inclusion' V := by ext y; rfl
    rw [← he, AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
    exact hb
  choose V hv b hb using h
  exact ⟨⟨V, hv, b, hb⟩⟩

def singularTwoPrimitiveCover [StronglyLocallyContractibleSpace X]
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2) : SingularTwoPrimitiveCover X c :=
  Classical.choice (nonempty_singularTwoPrimitiveCover X c)

variable {X} {c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2} (p : SingularTwoPrimitiveCover X c)

theorem SingularTwoPrimitiveCover.covers (x : X) : ∃ i, x ∈ p.cover i := ⟨x, p.mem_cover x⟩

def SingularTwoPrimitiveCover.overlapDifference (i j : X) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of ↥(p.cover i ⊓ p.cover j))).X 1 :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
    ((Opens.toTopCat X).map (homOfLE (inf_le_right : p.cover i ⊓ p.cover j ≤ p.cover j)))).f 1
      (p.primitive j) -
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
      ((Opens.toTopCat X).map (homOfLE (inf_le_left : p.cover i ⊓ p.cover j ≤ p.cover i)))).f 1
        (p.primitive i)

theorem SingularTwoPrimitiveCover.overlapDifference_closed (i j : X) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of ↥(p.cover i ⊓ p.cover j))).d 1 2
      (p.overlapDifference i j) = 0 := by
  let A := ModuleCat.of ℚ ℚ
  let fi := (Opens.toTopCat X).map (homOfLE (inf_le_left : p.cover i ⊓ p.cover j ≤ p.cover i))
  let fj := (Opens.toTopCat X).map (homOfLE (inf_le_right : p.cover i ⊓ p.cover j ≤ p.cover j))
  have hi := AlgebraicTopology.Cohomology.Singular.LocalPrimitives.cochainMap_primitive (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A fi) 1 _ _ (p.differential i)
  have hj := AlgebraicTopology.Cohomology.Singular.LocalPrimitives.cochainMap_primitive (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A fj) 1 _ _ (p.differential j)
  have he : fi ≫ Opens.inclusion' (p.cover i) = fj ≫ Opens.inclusion' (p.cover j) := by ext x; rfl
  rw [SingularTwoPrimitiveCover.overlapDifference, map_sub]
  erw [hj, hi]
  have hp := congrArg (fun f => f.f 2 c.val)
    (congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A) he)
  rw [AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp] at hp
  exact sub_eq_zero.mpr hp.symm

def SingularTwoPrimitiveCover.overlapCocycle (i j : X) :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (TopCat.of ↥(p.cover i ⊓ p.cover j)) 1 :=
  ⟨p.overlapDifference i j, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
    exact p.overlapDifference_closed i j⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.PrimitiveCover
