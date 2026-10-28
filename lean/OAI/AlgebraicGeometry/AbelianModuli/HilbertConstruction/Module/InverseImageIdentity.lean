import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageMates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.SheafInverseImageComposition

/-! # Inverse Image Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageIdentity

noncomputable section

/-! Compatibility of the actual inverse-image comparison with the identity morphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem moduleInverseImageSquare_id (X : Scheme.{u}) :
    (InverseImageMates.moduleInverseImageSquare (𝟙 X)).whiskerLeft (Scheme.Modules.pullbackId X).hom =
      (TwoSquare.vId (SheafOfModules.toSheaf X.ringCatSheaf)).whiskerRight
        (Additive.SheafInverseImageComposition.additiveSheafInverseImageIdIso X.carrier).hom := by
  let F : X.Modules ⥤ X.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf X.ringCatSheaf
  let P := Scheme.Modules.pullback (𝟙 X)
  let R := Scheme.Modules.pushforward (𝟙 X)
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{u} (𝟙 X.carrier)
  let A := TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 X.carrier)
  let s : TwoSquare F P L F := InverseImageMates.moduleInverseImageSquare (𝟙 X)
  let v : TwoSquare F (𝟭 X.Modules) (𝟭 (X.carrier.Sheaf AddCommGrpCat.{u})) F := TwoSquare.vId F
  let u : TwoSquare R F F A := InverseImageMates.moduleUnderlyingPushforwardSquare (𝟙 X)
  let pm : P ⟶ 𝟭 X.Modules := (Scheme.Modules.pullbackId X).hom
  let pa : L ⟶ 𝟭 (X.carrier.Sheaf AddCommGrpCat.{u}) := (Additive.SheafInverseImageComposition.additiveSheafInverseImageIdIso X.carrier).hom
  let rm : 𝟭 X.Modules ⟶ R := (Scheme.Modules.pushforwardId X).inv
  let ra : 𝟭 (X.carrier.Sheaf AddCommGrpCat.{u}) ⟶ A := (Additive.SheafInverseImageComposition.additiveSheafPushforwardIdIso X.carrier).inv
  let am := Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)
  let aa := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (𝟙 X.carrier)
  have ha : conjugateEquiv Adjunction.id aa pa = ra :=
    Adjunction.conjugateEquiv_leftAdjointIdIso_hom aa (Additive.SheafInverseImageComposition.additiveSheafPushforwardIdIso X.carrier)
  have hm : conjugateEquiv Adjunction.id am pm = rm :=
    Scheme.Modules.conjugateEquiv_pullbackId_hom X
  have hs : mateEquiv am aa s = u := InverseImageMates.moduleInverseImageSquare_mate (𝟙 X)
  have hl : mateEquiv Adjunction.id aa (s.whiskerLeft pm) = u.whiskerTop rm :=
    (conjugateEquiv_mateEquiv_vcomp Adjunction.id am aa pm s).trans
      (congrArg₂ (fun (w : TwoSquare R F F A) (r : 𝟭 X.Modules ⟶ R) =>
        w.whiskerTop r) hs hm)
  have hr : mateEquiv Adjunction.id aa (v.whiskerRight pa) =
      (mateEquiv Adjunction.id Adjunction.id v).whiskerBottom ra :=
    (mateEquiv_conjugateEquiv_vcomp Adjunction.id Adjunction.id aa v pa).trans
      (congrArg (fun r => (mateEquiv Adjunction.id Adjunction.id v).whiskerBottom r) ha)
  have hp : u.whiskerTop rm =
      (mateEquiv Adjunction.id Adjunction.id v).whiskerBottom ra := by
    ext M
    rfl
  change s.whiskerLeft pm = v.whiskerRight pa
  exact (mateEquiv Adjunction.id aa).injective (hl.trans (hp.trans hr.symm))

theorem moduleInverseImageComparison_id (X : Scheme.{u}) (M : X.Modules) :
    InverseImageComparison.moduleInverseImageComparison (𝟙 X) M ≫
      (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pullbackId X).hom.app M) =
    (Additive.SheafInverseImageComposition.additiveSheafInverseImageIdIso X.carrier).hom.app
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
  let F : X.Modules ⥤ X.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf X.ringCatSheaf
  let P := Scheme.Modules.pullback (𝟙 X)
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{u} (𝟙 X.carrier)
  let s : TwoSquare F P L F := InverseImageMates.moduleInverseImageSquare (𝟙 X)
  let v : TwoSquare F (𝟭 X.Modules) (𝟭 (X.carrier.Sheaf AddCommGrpCat.{u})) F := TwoSquare.vId F
  let pm : P ⟶ 𝟭 X.Modules := (Scheme.Modules.pullbackId X).hom
  let pa : L ⟶ 𝟭 (X.carrier.Sheaf AddCommGrpCat.{u}) := (Additive.SheafInverseImageComposition.additiveSheafInverseImageIdIso X.carrier).hom
  have h : (s.whiskerLeft pm).app M = (v.whiskerRight pa).app M :=
    congr_app (moduleInverseImageSquare_id X) M
  have hv : v.app M = 𝟙 (F.obj M) := Category.id_comp _
  have h' : s.app M ≫ F.map (pm.app M) = pa.app (F.obj M) :=
    h.trans ((congrArg (fun w => pa.app (F.obj M) ≫ w) hv).trans (Category.comp_id _))
  have hs : s.app M = InverseImageComparison.moduleInverseImageComparison (𝟙 X) M := InverseImageMates.moduleInverseImageSquare_app _ _
  exact (congrArg (fun w => w ≫ F.map (pm.app M)) hs).symm.trans h'

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageIdentity
