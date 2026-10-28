import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PullbackImmersion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportNeighborhoodDetection

/-! # Image Cohomology Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImageCohomologyDetection.BundleCycles

noncomputable section

/-! Equality after pullback to an open embedding detects equality on
its actual image. The proof uses the constructed inverse homeomorphism
and ordinary relative-cohomology functoriality. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {N T : Type} [TopologicalSpace N] [TopologicalSpace T]
    (f : N → T) (hf : Topology.IsOpenEmbedding f) (S : Set T)

local notation "U" => OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles.holomorphicOpenImage f hf
local notation "e" => OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph f hf

def openImageInverseMap : TopCat.of U ⟶ TopCat.of N :=
  TopCat.ofHom ⟨(e).symm, (e).symm.continuous⟩

theorem openImageInverseMap_comp :
    openImageInverseMap f hf ≫ PullbackImmersion.BundleCycles.openPullbackAmbientMap f hf =
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of T) (U : Set T) := by
  ext y
  exact congrArg Subtype.val ((e).apply_symm_apply y)

theorem openImageInverseMap_mapsTo : Set.MapsTo (openImageInverseMap f hf)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of T) S U) (f ⁻¹' S) := by
  intro y hy
  change f ((e).symm y) ∈ S
  have h := congrArg Subtype.val ((e).apply_symm_apply y)
  change f ((e).symm y) = y.val at h
  exact h.symm ▸ hy

theorem openImageRestriction_eq_of_pullback_eq (n : ℕ)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of T) S n)
    (hab : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (PullbackImmersion.BundleCycles.openPullbackAmbientMap f hf)
        (A := f ⁻¹' S) (B := S) (fun _ hy => hy) n a =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (PullbackImmersion.BundleCycles.openPullbackAmbientMap f hf)
        (A := f ⁻¹' S) (B := S) (fun _ hy => hy) n b) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of T) S U n a =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of T) S U n b := by
  let g := openImageInverseMap f hf
  have hg := openImageInverseMap_mapsTo f hf S
  have hcomp := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) g (PullbackImmersion.BundleCycles.openPullbackAmbientMap f hf)
    hg (show Set.MapsTo (PullbackImmersion.BundleCycles.openPullbackAmbientMap f hf) (f ⁻¹' S) S from fun _ hy => hy) n
  have hm := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr (openImageInverseMap_comp f hf)
    (show Set.MapsTo (g ≫ PullbackImmersion.BundleCycles.openPullbackAmbientMap f hf) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of T) S U) S
      from fun _ hy => hg hy) (fun _ hy => hy) n
  have ha := ConcreteCategory.congr_hom (hcomp.trans hm) a
  have hb := ConcreteCategory.congr_hom (hcomp.trans hm) b
  exact ha.symm.trans ((congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg n) hab).trans hb)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImageCohomologyDetection.BundleCycles
