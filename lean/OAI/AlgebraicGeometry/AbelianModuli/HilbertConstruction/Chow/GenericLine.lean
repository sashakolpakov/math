import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.AmpleLine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionPushforward
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoImage

/-! # Generic Line -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow

noncomputable section

/-! A line-bundle direct image on the constructed Chow model is a line bundle on its specified common open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

def Modification.ChowModification.Model.pushforwardLineOnCommon (D : Modification.ChowModification.Model f) (L : Line.Bundles.LineBundle D.scheme) :
    Line.Bundles.LineBundle D.cover.common.toScheme := by
  have : IsIso (D.projection ∣_ D.cover.common) := D.isIso_restrict
  exact (L.pullback (D.projection ⁻¹ᵁ D.cover.common).ι).pullback
    (inv (D.projection ∣_ D.cover.common))

def Modification.ChowModification.Model.pushforward_restrictCommon_iso (D : Modification.ChowModification.Model f) (L : Line.Bundles.LineBundle D.scheme) :
    (((pushforward D.projection).obj L.sheaf).restrict D.cover.common.ι) ≅
      (D.pushforwardLineOnCommon L).sheaf := by
  let q := D.projection ∣_ D.cover.common
  let V := D.projection ⁻¹ᵁ D.cover.common
  have : IsIso q := D.isIso_restrict
  exact Open.RestrictionPushforward.restrictPushforwardIsoOfIsPullbackApp D.projection q V.ι D.cover.common.ι
    (isPullback_morphismRestrict D.projection D.cover.common) L.sheaf ≪≫
      (pushforward q).mapIso ((restrictFunctorIsoPullback V.ι).app L.sheaf) ≪≫
        LineBundle.IsoImage.lineBundlePushforwardIso_of_isIso q (L.pullback V.ι)

theorem Modification.ChowModification.Model.amplePowerPushforward_isLine_onCommon (D : Modification.ChowModification.Model f) (n : ℕ) :
    ∃ L : Line.Bundles.LineBundle D.cover.common.toScheme,
      Nonempty ((((pushforward D.projection).obj (D.ampleLineBundle.tensorPower n).sheaf).restrict
        D.cover.common.ι) ≅ L.sheaf) :=
  ⟨D.pushforwardLineOnCommon (D.ampleLineBundle.tensorPower n),
    ⟨D.pushforward_restrictCommon_iso (D.ampleLineBundle.tensorPower n)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow
