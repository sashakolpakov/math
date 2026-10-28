import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSubdivisionHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSmallSpaces

/-! # Smooth Subdivision Small -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Subdivision and its homotopy on cover-small smooth chains

The cover-small smooth complex is itself the chain complex of a concrete
smooth simplex space. The already proved natural construction therefore
supplies both its subdivision and its homotopy, with exact inclusion
compatibility. This does not require any openness or covering hypothesis.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- All actual subdivision iterates agree with ordinary subdivision under inclusion. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_subdivision_iterate (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) (n N : ℕ)
    (c : (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X).X n) :
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X).f n (((SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision X).f n)^[N] c) =
      (SubdivisionOperator.Cycles.subdivisionDegree X.space n)^[N] ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X).f n c) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_subdivision_apply, ih,
      Function.iterate_succ_apply']

/-- Inclusion of cover-small smooth chains into all specified smooth chains. -/
abbrev SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type} (U : J → Set X.space) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U) ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X :=
  SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallInclusion X U)

/-- Forgetting both smallness and smoothness agrees with the two successive inclusions. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_inclusion (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type}
    (U : J → Set X.space) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion X U ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X = SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U) := by
  rw [SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion, SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_naturality]
  change SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U) ≫ LocalHomology.Cycles.integralSingularChainFunctor.map (𝟙 X.space) = _
  have hmap := LocalHomology.Cycles.integralSingularChainFunctor.map_id X.space
  exact (congrArg (fun f : LocalHomology.Cycles.integralSingularChains X.space ⟶ LocalHomology.Cycles.integralSingularChains X.space =>
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U) ≫ f) hmap).trans (Category.comp_id _)

/-- The concrete value form of the exact inclusion factorization. -/
@[simp]
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_inclusion_apply (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type}
    (U : J → Set X.space) (n : ℕ) (c : (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U)).X n) :
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X).f n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion X U).f n c) =
      (SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U)).f n c :=
  ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_inclusion X U)) c

/-- The small smooth chain inclusion is genuinely injective in every degree. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_injective (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type}
    (U : J → Set X.space) (n : ℕ) :
    Function.Injective ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion X U).f n) := by
  intro a b hab
  apply SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_injective (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U) n
  rw [← SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_inclusion_apply, ← SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_inclusion_apply, hab]

/-- Actual subdivision commutes with the actual small smooth inclusion. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_subdivision (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type}
    (U : J → Set X.space) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion X U ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision X =
      SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U) ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion X U := by
  apply HomologicalComplex.hom_ext
  intro n
  exact SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision_naturality (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallInclusion X U) n

/-- Every component of the actual smooth subdivision homotopy respects the
small inclusion. Both sides consist of actual cover-small smooth chains. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_subdivisionHomotopy (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type}
    (U : J → Set X.space) (i j : ℕ) :
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion X U).f i ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy X).hom i j =
      (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U)).hom i j ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion X U).f j :=
  SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy_naturality (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallInclusion X U) i j

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
