import OAI.AlgebraicGeometry.ComplexMultiplication.SectionOnOpenUnit
import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeNeighborhoodPullback

/-! # Relative Class Open Restriction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.RelativeClassOpenRestriction

noncomputable section

/-! # Pair-image transport of a global class is its actual open restriction -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.Topology Opposite OAI.AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B) (n : ℕ) (U : Opens X)
  (hU : hf.functor.obj ⊤ = U)

theorem relativeClassOnOpen_restriction
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set X) S) n) :
    SectionOnOpenUnit.relativeClassOnOpen f hf S B hB n U hU
      (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
        (RelativeNeighborhoodPullback.neighborhoodSupportPairMap ⟨f, f.hom.continuous⟩ B S hB
          Set.univ Set.univ (fun _ _ => Set.mem_univ _)) a) =
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
      (AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (Set.subset_univ (U : Set X)) S) a := by
  subst U
  let e := (AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologyPresheafOpenIso f hf S B hB n).app (op ⊤)
  let j := AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap
    (Set.subset_univ (hf.functor.obj ⊤ : Set X)) S
  let k := RelativeNeighborhoodPullback.neighborhoodSupportPairMap ⟨f, f.hom.continuous⟩ B S hB
    Set.univ Set.univ (fun _ _ => Set.mem_univ _)
  have hp : (AlgebraicTopology.Support.NeighborhoodPairImage.Singular.neighborhoodSupportPairImageIso f hf.isEmbedding Set.univ B S
      (fun y _ => by rw [← hB]; rfl)).hom ≫ j = k := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  have he : e.hom (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n j a) = AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n k a := by
    change AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
      (AlgebraicTopology.Support.NeighborhoodPairImage.Singular.neighborhoodSupportPairImageIso f hf.isEmbedding Set.univ B S
        (fun y _ => by rw [← hB]; rfl)).hom (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n j a) = _
    simpa only [AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp, LinearMap.comp_apply] using!
      congrArg (fun g => AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n g a) hp
  unfold SectionOnOpenUnit.relativeClassOnOpen
  simp only [eqToHom_refl, op_id]
  have hi : (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n).map (𝟙 (op (hf.functor.obj ⊤)))
      (e.inv (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n k a)) = e.inv (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n k a) := by
    simpa only [ConcreteCategory.id_apply] using! ConcreteCategory.congr_hom
      ((AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n).map_id (op (hf.functor.obj ⊤)))
      (e.inv (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n k a))
  apply Eq.trans hi
  rw [← he]
  exact e.addCommGroupIsoToAddEquiv.symm_apply_apply _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.RelativeClassOpenRestriction
