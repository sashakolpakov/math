import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlas
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverOpenCoverGluing

/-! # Atlas Global Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.AtlasGlobalClassification

noncomputable section

/-! Global classification on reduced tests follows from local chart
classification and separation of the actual functor on the source cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

namespace ReducedRepresentationAtlas
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, OpenRepresentations.ReducedOpenRepresentation F (U i))

theorem classifies_of_source_cover (u : F.obj (op (RepresentationAtlas.ReducedRepresentationAtlas.over D)))
    (hu : ∀ i, F.map (RepresentationAtlas.ReducedRepresentationAtlas.chartOver D i).op u = (D i).sectionValue)
    (T : Over S) [IsReduced T.left] (C : T.left.OpenCover) (c : C.I₀ → I)
    (hc : ∀ i, ∀ x : (C.X i), (OverOpenCoverGluing.OverOpenCover.obj T C i).hom x ∈ U (c i))
    (hsep : Function.Injective (fun v : F.obj (op T) =>
      fun i => F.map (OverOpenCoverGluing.OverOpenCover.inclusion T C i).op v)) :
    Function.Bijective (fun f : T ⟶ RepresentationAtlas.ReducedRepresentationAtlas.over D => F.map f.op u) := by
  have hloc (i) := RepresentationAtlas.ReducedRepresentationAtlas.classifies_on_base_open D u (c i) (hu (c i)) (OverOpenCoverGluing.OverOpenCover.obj T C i) (hc i)
  apply (Function.bijective_iff_existsUnique _).mpr
  intro v
  choose f hf using fun i => (hloc i).surjective (F.map (OverOpenCoverGluing.OverOpenCover.inclusion T C i).op v)
  have hm (i j) : OverOpenCoverGluing.OverOpenCover.overlapLeft T C i j ≫ f i =
      OverOpenCoverGluing.OverOpenCover.overlapRight T C i j ≫ f j := by
    have hT : ∀ x : (OverOpenCoverGluing.OverOpenCover.overlap T C i j).left,
        (OverOpenCoverGluing.OverOpenCover.overlap T C i j).hom x ∈ U (c i) := fun x => by
      have h := hc i ((OverOpenCoverGluing.OverOpenCover.overlapLeft T C i j).left x)
      exact (congrArg (fun q : (OverOpenCoverGluing.OverOpenCover.overlap T C i j).left ⟶ S => q x)
        (OverOpenCoverGluing.OverOpenCover.overlapLeft T C i j).w) ▸ h
    apply (RepresentationAtlas.ReducedRepresentationAtlas.classifies_on_base_open D u (c i) (hu (c i)) (OverOpenCoverGluing.OverOpenCover.overlap T C i j) hT).injective
    simp only [op_comp, F.map_comp, types_comp_apply, hf]
    simpa only [op_comp, F.map_comp, types_comp_apply] using
      congrArg (fun q : OverOpenCoverGluing.OverOpenCover.overlap T C i j ⟶ T => F.map q.op v)
        (OverOpenCoverGluing.OverOpenCover.overlap_condition T C i j)
  obtain ⟨q, hq, _⟩ := OverOpenCoverGluing.OverOpenCover.existsUnique_glued_morphism T C f hm
  have hv : F.map q.op u = v := by
    apply hsep
    funext i
    change F.map (OverOpenCoverGluing.OverOpenCover.inclusion T C i).op (F.map q.op u) = _
    rw [← F.map_comp_apply]
    change F.map (OverOpenCoverGluing.OverOpenCover.inclusion T C i ≫ q).op u = _
    rw [hq i]
    exact hf i
  refine ⟨q, hv, fun r hr => ?_⟩
  apply OverOpenCoverGluing.OverOpenCover.hom_ext T C
  intro i
  apply (hloc i).injective
  simp only [op_comp, F.map_comp, types_comp_apply, hr, hv]

end ReducedRepresentationAtlas

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.AtlasGlobalClassification
