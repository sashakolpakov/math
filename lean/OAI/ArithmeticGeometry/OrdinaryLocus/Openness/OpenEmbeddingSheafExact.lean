import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenSheafExact
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyTransport

/-! # Open Embedding Sheaf Exact -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenEmbeddingSheafExact.Construction

noncomputable section

/-! Exact restriction along open embeddings and global-section comparison for homeomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : Topology.IsOpenEmbedding f)

abbrev openEmbeddingAbelianPullback : AbelianSheafInjectives.Construction.AbelianSheaves Y ⥤ AbelianSheafInjectives.Construction.AbelianSheaves X :=
  haveI := hf.functor_isContinuous
  hf.isOpenMap.functor.sheafPushforwardContinuous AddCommGrpCat.{u}
    (_root_.Opens.grothendieckTopology X) (_root_.Opens.grothendieckTopology Y)

instance openEmbeddingAbelianPullback_isLeftAdjoint :
    (openEmbeddingAbelianPullback hf).IsLeftAdjoint := by
  have hcont := hf.functor_isContinuous
  have hright : (Opens.map f).IsContinuous
      (_root_.Opens.grothendieckTopology Y) (_root_.Opens.grothendieckTopology X) := by
    apply Functor.isContinuous_of_coverPreserving
    · exact compatiblePreserving_opens_map f
    · exact coverPreserving_opens_map f
  exact (hf.isOpenMap.adjunction.sheafPushforwardContinuous
    (E := AddCommGrpCat.{u}) (_root_.Opens.grothendieckTopology X)
    (_root_.Opens.grothendieckTopology Y)).isLeftAdjoint

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts in
instance openEmbeddingAbelianPullback_additive : (openEmbeddingAbelianPullback hf).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

theorem openEmbeddingAbelianPullback_shortExact
    (S : ShortComplex (AbelianSheafInjectives.Construction.AbelianSheaves Y)) (hS : S.ShortExact) :
    (S.map (openEmbeddingAbelianPullback hf)).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  exact hS.map _

theorem surjective_openEmbedding_image_top (hsurj : Function.Surjective f) :
    hf.isOpenMap.functor.obj ⊤ = ⊤ := by
  ext y
  change y ∈ f '' (Set.univ : Set X) ↔ y ∈ (Set.univ : Set Y)
  simp [Set.image_univ, Set.range_eq_univ.mpr hsurj]

def surjectiveOpenEmbeddingSectionsIso (hsurj : Function.Surjective f) :
    openEmbeddingAbelianPullback hf ⋙
      CohomologyTransport.Construction.abelianSheafSections (_root_.Opens.grothendieckTopology X) ⊤ ≅
    CohomologyTransport.Construction.abelianSheafSections (_root_.Opens.grothendieckTopology Y) ⊤ := by
  refine NatIso.ofComponents (fun F ↦ F.obj.mapIso
    (eqToIso (congrArg op (surjective_openEmbedding_image_top hf hsurj)))) ?_
  intro F G φ
  exact (φ.hom.naturality
    (eqToHom (congrArg op (surjective_openEmbedding_image_top hf hsurj)))).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenEmbeddingSheafExact.Construction
