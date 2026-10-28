import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularMapGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

/-! # Regular Map Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! A morphism with the prescribed native framed local formula has
exactly that regular coefficient in the original section coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem LineFrameAtlas.LocalLineFrame.coordinates_over_restricted {X : Scheme.{0}} {M : X.Modules}
    (r : LineFrameAtlas.LocalLineFrame M) (U : X.Opens) (hr : U ≤ r.domain) (x : Γ(M, U)) :
    r.coordinates U hr x =
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr r.frame)).hom.val.app
        (.op (Over.mk (𝟙 U))) x :=
  (Intrinsic.FrameCoordinates.frameOnOpen_native_restrict M r.domain r.frame U hr x).symm.trans
    (Intrinsic.FrameCoordinates.frameOnOpen_over M U (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr r.frame) U le_rfl x)

theorem Intrinsic.RegularMapCoordinates.lineMorphismCoefficient_of_nativeFramedRegularMap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) (f : L.sheaf ⟶ K.sheaf) (U : V.carrier.Opens)
    (r : LineFrameAtlas.LocalLineFrame L.sheaf) (s : LineFrameAtlas.LocalLineFrame K.sheaf)
    (hr : U ≤ r.domain) (hs : U ≤ s.domain) (a : Γ(V.carrier, U))
    (hf : f.over U = Intrinsic.RegularMapGluing.nativeFramedRegularMap V L K U r s hr hs a) :
    LineFrameAtlas.lineMorphismCoefficient f r s U hr hs = a := by
  let e := SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso L.sheaf U
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr r.frame)
  let g := SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso K.sheaf U
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame)
  let x := (r.coordinates U hr).symm 1
  have he : e.hom.val.app (.op (Over.mk (𝟙 U))) x = (1 : Γ(V.carrier, U)) :=
    (r.coordinates_over_restricted U hr x).symm.trans (LinearEquiv.apply_symm_apply _ _)
  have hcomp : f.over U ≫ g.hom = e.hom ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd V.carrier.ringCatSheaf U a := by
    change f.over U = FramedRegularMapGluing.framedRegularMap L.sheaf K.sheaf U e g a at hf
    rw [hf]
    simp only [FramedRegularMapGluing.framedRegularMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := congrArg (fun q => q.val.app (.op (Over.mk (𝟙 U))) x) hcomp
  change g.hom.val.app (.op (Over.mk (𝟙 U))) (f.app U x) =
    (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd V.carrier.ringCatSheaf U a).val.app (.op (Over.mk (𝟙 U)))
      (e.hom.val.app (.op (Over.mk (𝟙 U))) x) at hv
  rw [he] at hv
  erw [SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd_app_apply] at hv
  change (show Γ(V.carrier, U) from g.hom.val.app (.op (Over.mk (𝟙 U))) (f.app U x)) =
    (1 : Γ(V.carrier, U)) * V.carrier.presheaf.map (𝟙 (.op U)) a at hv
  erw [V.carrier.presheaf.map_id, ConcreteCategory.id_apply, one_mul] at hv
  exact (s.coordinates_over_restricted U hs (f.app U x)).trans hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
