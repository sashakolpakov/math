import OAI.AlgebraicGeometry.FormalGeometry.Completion.TautologicalFrameClassification

/-! # Classified Frame Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Every actual line-bundle trivialization is recovered by pulling
back the universal frame along its own classifying morphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.trivializationPointEquiv_top_congr {Y T : Scheme.{u}} [IsAffine T]
    (f f' : Y ⟶ X) (hf : f = f') (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ π g) (hp' : IsPullback f' ρ π g)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    D.lineBundleTrivializationPointEquiv f' ρ g hp' (e ≪≫ (Scheme.Modules.pullbackCongr hf).app L.sheaf) =
      D.lineBundleTrivializationPointEquiv f ρ g hp e := by
  subst f'
  have he : e ≪≫ (Scheme.Modules.pullbackCongr (rfl : f = f)).app L.sheaf = e := by
    apply Iso.ext
    change e.hom ≫ 𝟙 _ = e.hom
    exact Category.comp_id _
  exact congrArg (D.lineBundleTrivializationPointEquiv f ρ g hp) he

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.trivializationPointEquiv_base_congr_left {Y T : Scheme.{u}} [IsAffine T]
    (f : Y ⟶ X) (ρ : Y ⟶ T) (g g' : T ⟶ S) (hg : g = g')
    (hp : IsPullback f ρ π g) (hp' : IsPullback f ρ π g')
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    (D.lineBundleTrivializationPointEquiv f ρ g' hp' e).left =
      (D.lineBundleTrivializationPointEquiv f ρ g hp e).left := by
  subst g'
  rfl

variable {Y T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S)
  (hp : IsPullback f ρ π g) (p : Over.mk g ⟶ D.frameSchemeOverBase)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameClassifierFamilyMap : Y ⟶ D.frameFamily :=
  D.frameFamily_isPullback.lift f (ρ ≫ p.left) (by rw [Category.assoc, p.w]; exact hp.w)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameClassifierFamilyMap_fst : D.frameClassifierFamilyMap f ρ g hp p ≫ D.frameFamilyToOriginal = f :=
  D.frameFamily_isPullback.lift_fst _ _ _

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameClassifierFamilyMap_snd : D.frameClassifierFamilyMap f ρ g hp p ≫ D.frameFamilyProjection = ρ ≫ p.left :=
  D.frameFamily_isPullback.lift_snd _ _ _

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameClassifierFamilyMap_isPullback :
    IsPullback (D.frameClassifierFamilyMap f ρ g hp p) ρ D.frameFamilyProjection p.left := by
  refine IsPullback.of_right (t := D.frameFamily_isPullback) ?_ (D.frameClassifierFamilyMap_snd f ρ g hp p)
  rw [D.frameClassifierFamilyMap_fst, p.w]
  exact hp

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifiedFramePullback : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf :=
  Frame.SchemeNaturality.Construction.compositeLineFrameIso D.frameFamilyToOriginal (D.frameClassifierFamilyMap f ρ g hp p) L.sheaf D.tautologicalFrame ≪≫
    (Scheme.Modules.pullbackCongr (D.frameClassifierFamilyMap_fst f ρ g hp p)).app L.sheaf

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifiedFramePullback_classifies [IsAffine T] :
    D.lineBundleTrivializationPointEquiv f ρ g hp (D.classifiedFramePullback f ρ g hp p) = p := by
  let k := D.frameClassifierFamilyMap f ρ g hp p
  have hf := D.frameClassifierFamilyMap_fst f ρ g hp p
  have hk := D.frameClassifierFamilyMap_snd f ρ g hp p
  have ho := (D.frameClassifierFamilyMap_isPullback f ρ g hp p).paste_horiz D.frameFamily_isPullback
  have hp' : IsPullback f ρ π (p.left ≫ D.frameSchemeOverBase.hom) := by rw [p.w]; exact hp
  have hc := D.tautologicalFrame_pullback_classifies k ρ p.left hk ho
  have ht := D.trivializationPointEquiv_top_congr (k ≫ D.frameFamilyToOriginal) f hf ρ
    (p.left ≫ D.frameSchemeOverBase.hom) ho hp'
      (Frame.SchemeNaturality.Construction.compositeLineFrameIso D.frameFamilyToOriginal k L.sheaf D.tautologicalFrame)
  have hb := D.trivializationPointEquiv_base_congr_left f ρ (p.left ≫ D.frameSchemeOverBase.hom) g p.w hp' hp
    (D.classifiedFramePullback f ρ g hp p)
  apply Over.OverMorphism.ext
  exact hb.trans ((congrArg Over.Hom.left ht).trans (congrArg Over.Hom.left hc))

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifiedFramePullback_recovers [IsAffine T]
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    D.classifiedFramePullback f ρ g hp (D.lineBundleTrivializationPointEquiv f ρ g hp e) = e :=
  (D.lineBundleTrivializationPointEquiv f ρ g hp).injective
    (D.classifiedFramePullback_classifies f ρ g hp (D.lineBundleTrivializationPointEquiv f ρ g hp e))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
