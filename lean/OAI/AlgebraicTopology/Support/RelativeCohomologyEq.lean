/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.Support.RelativeCohomologySheaf

/-! # Relative Cohomology Eq -/

namespace OAI.AlgebraicTopology.Support.RelativeCohomologyEq.Singular

noncomputable section

open _root_.AlgebraicTopology

/-!
# The local relative-cohomology presheaf and its sheafification

-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open _root_.TopCat.Presheaf

variable {M : Type} [TopologicalSpace M]

variable (X : TopCat.{0}) (S : Set X) (n : ℕ)

@[simp] theorem supportRelativeCohomologyPresheaf_map_apply {U V : Opens X}
    (hUV : U ≤ V) (a : Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (V : Set X) S) n) :
    (RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n).map (homOfLE hUV).op a =
      Singular.Cohomology.relativeCohomologyMap ℚ n
        (LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (W := (U : Set X)) (V := (V : Set X)) hUV S) a := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction followed by germ is the original germ; the restriction is the
pair-inclusion pullback. -/
theorem supportRelativeCohomologyGerm_restrict {U V : Opens X} (hUV : U ≤ V)
    (x : X) (hx : x ∈ U)
    (a : Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (V : Set X) S) n) :
    RelativeCohomologySheaf.Singular.supportRelativeCohomologyGerm X S n U x hx
      (Singular.Cohomology.relativeCohomologyMap ℚ n
        (LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (W := (U : Set X)) (V := (V : Set X)) hUV S) a) =
    RelativeCohomologySheaf.Singular.supportRelativeCohomologyGerm X S n V x (hUV hx) a := by
  have h := ConcreteCategory.congr_hom
    ((RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf X S n).naturality (homOfLE hUV).op) a
  exact (congrArg ((RelativeCohomologySheaf.Singular.supportRelativeCohomologySheaf X S n).presheaf.germ U x hx) h).trans
    ((RelativeCohomologySheaf.Singular.supportRelativeCohomologySheaf X S n).presheaf.germ_res_apply (homOfLE hUV) x hx _)

/-- Equality after restriction to a common neighborhood gives equal sheaf germs. -/
theorem supportRelativeCohomologyGerm_eq_of_restrict_eq
    {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V) (x : X) (hx : x ∈ W)
    (a : Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (U : Set X) S) n)
    (b : Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (V : Set X) S) n)
    (h : Singular.Cohomology.relativeCohomologyMap ℚ n
        (LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (U : Set X)) hWU S) a =
      Singular.Cohomology.relativeCohomologyMap ℚ n
        (LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (V : Set X)) hWV S) b) :
    RelativeCohomologySheaf.Singular.supportRelativeCohomologyGerm X S n U x (hWU hx) a =
      RelativeCohomologySheaf.Singular.supportRelativeCohomologyGerm X S n V x (hWV hx) b := by
  rw [← supportRelativeCohomologyGerm_restrict X S n hWU x hx,
    ← supportRelativeCohomologyGerm_restrict X S n hWV x hx, h]

/-- When a neighborhood misses the support, its relative-chain complex is zero. -/
theorem neighborhoodSupportRelativeChains_isZero (V : Set X) (hV : ∀ x ∈ V, x ∉ S) :
    IsZero ((Singular.Cohomology.relativeChainFunctor ℚ).obj (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair V S)) := by
  have hset : {v : V | v.1 ∉ S} = Set.univ := Set.eq_univ_of_forall fun v => hV v.1 v.2
  change IsZero ((Singular.Cohomology.relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of V) _))
  rw [hset]
  let P := TopPair.ofSubset (X := TopCat.of V) (Set.univ : Set V)
  have hPi : IsIso P.map :=
    (TopCat.isIso_iff_isHomeomorph P.map).mpr (Homeomorph.Set.univ V).isHomeomorph
  have hchain : IsIso ((Singular.Cohomology.chainPairFunctor ℚ).obj P).hom := by
    change IsIso (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map P.map)
    infer_instance
  exact isZero_cokernel_of_epi ((Singular.Cohomology.chainPairFunctor ℚ).obj P).hom

/-- Relative cohomology vanishes on neighborhoods disjoint from the support. -/
theorem neighborhoodSupportRelativeCohomology_subsingleton
    (V : Set X) (hV : ∀ x ∈ V, x ∉ S) :
    Subsingleton (Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair V S) n) := by
  have hh : IsZero (Singular.Cohomology.RelativeHomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair V S) n) :=
    (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_isZero
      (neighborhoodSupportRelativeChains_isZero X S V hV)
  exact Singular.CohomologyTo.relativeCohomology_subsingleton ℚ _ n (ModuleCat.subsingleton_of_isZero hh)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Off closed support, every local relative class has zero sheaf germ. -/
theorem supportRelativeCohomologyGerm_eq_zero_of_not_mem (hS : IsClosed S)
    (V : Opens X) (x : X) (hx : x ∈ V) (hxS : x ∉ S)
    (a : Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (V : Set X) S) n) :
    RelativeCohomologySheaf.Singular.supportRelativeCohomologyGerm X S n V x hx a = 0 := by
  let W : Opens X := V ⊓ ⟨Sᶜ, hS.isOpen_compl⟩
  have hWV : W ≤ V := inf_le_left
  have hxW : x ∈ W := ⟨hx, hxS⟩
  let := neighborhoodSupportRelativeCohomology_subsingleton X S n W (fun _ hy => hy.2)
  rw [← supportRelativeCohomologyGerm_restrict X S n hWV x hxW]
  have hz : Singular.Cohomology.relativeCohomologyMap ℚ n
      (LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (V : Set X)) hWV S) a = 0 :=
    Subsingleton.elim _ _
  rw [hz]
  simp only [RelativeCohomologySheaf.Singular.supportRelativeCohomologyGerm, map_zero]

end

end OAI.AlgebraicTopology.Support.RelativeCohomologyEq.Singular
