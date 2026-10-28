import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PicardImageIso

/-! # Geometric Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GeometricSections.Construction

noncomputable section

/-! A geometric Picard-image isomorphism lifts sections of the original
Picard sheaf at the original geometric parameter, with no replacement
of its classifying map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S S' : Scheme.{u}} {B Q : Over S} [GrpObj B] [GrpObj Q]
  (i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)

omit [GrpObj Q] in
theorem picardImage_section_natural {T U : Over S} (a : U ⟶ T) (x : T ⟶ Q) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map a.op (i.app (op T) (ULift.up x)) =
      i.app (op U) (ULift.up (a ≫ x)) :=
  (congrArg (fun b : (uliftYoneda.{u + 1}.obj Q).obj (op T) ⟶
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op U) => b (ULift.up x)) (i.naturality a.op)).symm

theorem picardImage_sections_surjective_of_baseChange (s : S' ⟶ S)
    [IsIso (BaseChange.Construction.picardImageBaseChangeMap i s)] (T : Over S') :
    Function.Surjective (i.app (op ((Over.map s).obj T))) := by
  intro y
  have hs : Function.Surjective ((BaseChange.Construction.picardImageBaseChangeMap i s).app (op T)) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).surjective
  obtain ⟨x, hx⟩ := hs ((Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv B s T).symm y)
  refine ⟨ULift.up (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv Q s T x.down), ?_⟩
  exact (BaseChange.Construction.picardImageBaseChangeMap_value i s T x.down).symm.trans
    ((congrArg (Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv B s T) hx).trans
      ((Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv B s T).apply_symm_apply y))

omit [GrpObj Q] in
theorem picardImage_sections_surjective_of_parameterIso {T U : Over S} (e : T ≅ U)
    (h : Function.Surjective (i.app (op T))) : Function.Surjective (i.app (op U)) := by
  intro y
  obtain ⟨x, hx⟩ := h ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map e.hom.op y)
  refine ⟨ULift.up (e.inv ≫ x.down), ?_⟩
  refine (picardImage_section_natural i e.inv x.down).symm.trans
    ((congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map e.inv.op) hx).trans ?_)
  rw [← Functor.map_comp_apply]
  simp only [← op_comp, e.inv_hom_id, op_id, Functor.map_id_apply]

theorem picardImage_geometric_sections_surjective
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ S)
    [IsIso (BaseChange.Construction.picardImageBaseChangeMap i s)] : Function.Surjective (i.app (op (Over.mk s))) := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 _)
  let e : (Over.map s).obj T ≅ Over.mk s := Over.isoMk (Iso.refl _) (by simp [T])
  exact picardImage_sections_surjective_of_parameterIso i e
    (picardImage_sections_surjective_of_baseChange i s T)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GeometricSections.Construction
