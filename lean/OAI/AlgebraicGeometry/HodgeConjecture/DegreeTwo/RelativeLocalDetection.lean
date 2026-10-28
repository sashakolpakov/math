import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportedGerms

/-! # Relative Local Detection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeLocalDetection.Constructions

noncomputable section

/-!
# DegreeTwo: local detection through actual open embeddings

An actual open embedding identifies its source pair with its open image.
Equality after its pullback therefore gives equality on a genuine ambient
open. The actual supported cohomology sheaf then detects local equality.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.CycleClass.Geometric.SupportedGerms.Cycles OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})

/-- Pullback equality along an actual open embedding gives equality on
its actual ambient open image. -/
theorem relativeClass_eq_on_openEmbedding_range (A : Set X) (n : ℕ)
    {Y : TopCat.{0}} (f : Y ⟶ X) (hf : Topology.IsOpenEmbedding f)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n)
    (hab : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f (A := f ⁻¹' A) (fun _ hx => hx) n a =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f (A := f ⁻¹' A) (fun _ hx => hx) n b) :
    ∃ W : Opens X, (W : Set X) = Set.range f ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction M X A W n a =
        CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction M X A W n b := by
  let W : Opens X := ⟨Set.range f, hf.isOpen_range⟩
  let e : Y ≃ₜ TopCat.of W := hf.isEmbedding.toHomeomorph
  have he : (TopCat.isoOfHomeo (X := Y) (Y := TopCat.of W) e).hom ≫
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (W : Set X) = f := by
    ext y
    exact hf.isEmbedding.toHomeomorph_apply_coe y
  have hp : ∀ y : Y, y ∈ f ⁻¹' A ↔ e y ∈ AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A W := by
    intro y
    change f y ∈ A ↔ (e y).val ∈ A
    rw [hf.isEmbedding.toHomeomorph_apply_coe]
  let E : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of W) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A W) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y (f ⁻¹' A) n :=
    AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso M (X := Y) (Y := TopCat.of W)
      e (f ⁻¹' A) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A W) hp n
  have hc : CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction M X A W n ≫ E.hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f (A := f ⁻¹' A) (fun _ hx => hx) n := by
    have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp M
      (TopCat.isoOfHomeo (X := Y) (Y := TopCat.of W) e).hom
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (W : Set X)) (fun y hy => (hp y).mp hy) (fun _ hx => hx) n
    simp only [he] at h
    exact h
  refine ⟨W, rfl, ?_⟩
  apply E.toLinearEquiv.injective
  exact (ConcreteCategory.congr_hom hc a).trans
    (hab.trans (ConcreteCategory.congr_hom hc b).symm)

/-- Local equality of restrictions of global relative classes is
detected by the actual supported sheaf wherever the section map is mono. -/
theorem relativeClass_restrict_eq_of_local_restrictions (O U : Opens X) (n : ℕ)
    [Mono (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O U n)]
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (O : Set X) n)
    (hab : ∀ (x : X), x ∈ U → x ∉ O →
      ∃ W : Opens X, x ∈ W ∧
        CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction M X (O : Set X) W n a =
          CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction M X (O : Set X) W n b) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction M X (O : Set X) U n a =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction M X (O : Set X) U n b := by
  let S := ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
  have image (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (O : Set X) n) (W : Opens X) :
      S.map (homOfLE (le_top : W ≤ ⊤)).op (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap M X O n c) =
        CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O W n
          (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction M X (O : Set X) W n c) :=
    ConcreteCategory.congr_hom (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict M X O W n) c
  apply (ModuleCat.mono_iff_injective (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O U n)).mp inferInstance
  rw [← image a U, ← image b U]
  apply CycleClass.Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support M X O U n
  intro x hxU hxO
  obtain ⟨W, hxW, hW⟩ := hab x hxU hxO
  have hSW : S.map (homOfLE (le_top : W ≤ ⊤)).op
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap M X O n a) =
      S.map (homOfLE (le_top : W ≤ ⊤)).op
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap M X O n b) := by
    rw [image a W, image b W, hW]
  have hg := congrArg (TopCat.Presheaf.germ S W x hxW) hSW
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact hg

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeLocalDetection.Constructions
