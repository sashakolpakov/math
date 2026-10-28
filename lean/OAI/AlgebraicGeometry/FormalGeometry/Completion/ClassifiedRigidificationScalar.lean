import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClassifiedFramePullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.UniversalRigidificationScalar

/-! # Classified Rigidification Scalar -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Evaluating the universal rigidification function at a classifying
morphism gives the actual rigidification scalar of that frame. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  {Y T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
  (p : Over.mk g ⟶ D.frameSchemeOverBase) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
  (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T) (h : b ≫ f = g ≫ s)

include hb h in
theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameClassifierFamilyMap_axis :
    b ≫ D.frameClassifierFamilyMap f ρ g hp p = p.left ≫ D.frameAxis s hs := by
  apply D.frameFamily_isPullback.hom_ext
  · calc
      (b ≫ D.frameClassifierFamilyMap f ρ g hp p) ≫ D.frameFamilyToOriginal = b ≫ f := by
        rw [Category.assoc, D.frameClassifierFamilyMap_fst]
      _ = g ≫ s := h
      _ = (p.left ≫ D.frameSchemeOverBase.hom) ≫ s := congrArg (fun z : T ⟶ S => z ≫ s) p.w.symm
      _ = (p.left ≫ D.frameAxis s hs) ≫ D.frameFamilyToOriginal := by
        simp only [Category.assoc, D.frameAxis_fst]
  · calc
      (b ≫ D.frameClassifierFamilyMap f ρ g hp p) ≫ D.frameFamilyProjection = b ≫ (ρ ≫ p.left) := by
        rw [Category.assoc, D.frameClassifierFamilyMap_snd]
      _ = p.left := by rw [← Category.assoc, hb, Category.id_comp]
      _ = (p.left ≫ D.frameAxis s hs) ≫ D.frameFamilyProjection := by
        rw [Category.assoc, D.frameAxis_snd, Category.comp_id]

include hb in
theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifiedFramePullback_scalar
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) :
    Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h L.sheaf r (D.classifiedFramePullback f ρ g hp p) =
      p.left.appTop (D.rigidificationScalar s hs r) := by
  let k := D.frameClassifierFamilyMap f ρ g hp p
  let e₀ := Frame.SchemeNaturality.Construction.compositeLineFrameIso D.frameFamilyToOriginal k L.sheaf D.tautologicalFrame
  have hf := D.frameClassifierFamilyMap_fst f ρ g hp p
  have h' : b ≫ f = (p.left ≫ D.frameSchemeOverBase.hom) ≫ s := by rw [p.w]; exact h
  have hx : b ≫ (k ≫ D.frameFamilyToOriginal) = (p.left ≫ D.frameSchemeOverBase.hom) ≫ s :=
    (congrArg (fun z : Y ⟶ X => b ≫ z) hf).trans h'
  have hn := RigidificationScalarNaturality.Construction.frameAxisScalar_baseChange D.frameFamilyToOriginal k s (D.frameAxis s hs)
    D.frameSchemeOverBase.hom b p.left (D.frameClassifierFamilyMap_axis f ρ g hp p s hs b hb h)
      (D.frameAxis_fst s hs) hx L.sheaf r D.tautologicalFrame
  have ht := ComposedSectionAssociativity.Construction.frameAxisScalar_congr_top (k ≫ D.frameFamilyToOriginal) f hf b
    (p.left ≫ D.frameSchemeOverBase.hom) s hx h' L.sheaf r e₀
  have hg := ComposedSectionAssociativity.Construction.frameAxisScalar_congr_base f b (p.left ≫ D.frameSchemeOverBase.hom) g p.w s h' h L.sheaf r
    (D.classifiedFramePullback f ρ g hp p)
  exact hg.trans (ht.trans hn)

omit p in
include hb in
theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameAxisScalar_classifier [IsAffine T]
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h L.sheaf r e =
      (D.lineBundleTrivializationPointEquiv f ρ g hp e).left.appTop (D.rigidificationScalar s hs r) := by
  have hc := D.classifiedFramePullback_scalar f ρ g hp (D.lineBundleTrivializationPointEquiv f ρ g hp e)
    s hs b hb h r
  have he := congrArg (Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h L.sheaf r) (D.classifiedFramePullback_recovers f ρ g hp e)
  exact he.symm.trans hc

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
