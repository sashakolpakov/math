import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalPullback

/-! # Product Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProductLocalization

noncomputable section

/-! Principal localization of an actual crystalline product is the product with the localized factor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {U V : BigCrystallineSite.Object p B J δ f} (P : BinaryFan U V) (hP : IsLimit P) (r : U.ring)

def cone : BinaryFan (Localization.object U r) V :=
  BinaryFan.mk (LocalizationMaps.localizedHom P.fst r) (Localization.hom P.pt (P.fst.ringMap r) ≫ P.snd)

def baseLift (s : BinaryFan (Localization.object U r) V) : s.pt ⟶ P.pt :=
  hP.lift (BinaryFan.mk (s.fst ≫ Localization.hom U r) s.snd)

theorem baseLift_fst (s : BinaryFan (Localization.object U r) V) : baseLift P hP r s ≫ P.fst = s.fst ≫ Localization.hom U r :=
  hP.fac (BinaryFan.mk (s.fst ≫ Localization.hom U r) s.snd) ⟨WalkingPair.left⟩

theorem baseLift_snd (s : BinaryFan (Localization.object U r) V) : baseLift P hP r s ≫ P.snd = s.snd :=
  hP.fac (BinaryFan.mk (s.fst ≫ Localization.hom U r) s.snd) ⟨WalkingPair.right⟩

theorem baseLift_unit (s : BinaryFan (Localization.object U r) V) : IsUnit ((baseLift P hP r s).ringMap (P.fst.ringMap r)) := by
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Ring U r) r).map s.fst.ringMap.toRingHom
  have he := congrArg (fun a : s.pt ⟶ U => a.ringMap r) (baseLift_fst P hP r s)
  exact he.symm ▸ hu

def lift (s : BinaryFan (Localization.object U r) V) : s.pt ⟶ (cone P r).pt :=
  LocalizationLift.liftHom (baseLift P hP r s) (P.fst.ringMap r) (baseLift_unit P hP r s)

theorem lift_fst (s : BinaryFan (Localization.object U r) V) : ProductLocalization.lift P hP r s ≫ (cone P r).fst = s.fst := by
  apply (cancel_mono (Localization.hom U r)).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun b => ProductLocalization.lift P hP r s ≫ b) (LocalizationMaps.localizedHom_square P.fst r)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun b => b ≫ P.fst)
          (LocalizationLift.liftHom_comp (baseLift P hP r s) (P.fst.ringMap r) (baseLift_unit P hP r s))).trans
            (baseLift_fst P hP r s))))

theorem lift_snd (s : BinaryFan (Localization.object U r) V) : ProductLocalization.lift P hP r s ≫ (cone P r).snd = s.snd := by
  change LocalizationLift.liftHom (baseLift P hP r s) (P.fst.ringMap r) _ ≫ (Localization.hom P.pt (P.fst.ringMap r) ≫ P.snd) = _
  rw [← Category.assoc, LocalizationLift.liftHom_comp, baseLift_snd]

def isProduct : IsLimit (cone P r) := by
  apply BinaryFan.isLimitMk (ProductLocalization.lift P hP r) (lift_fst P hP r) (lift_snd P hP r)
  intro s a ha hb
  apply (cancel_mono (Localization.hom P.pt (P.fst.ringMap r))).mp
  change a ≫ Localization.hom P.pt (P.fst.ringMap r) =
    LocalizationLift.liftHom (baseLift P hP r s) (P.fst.ringMap r) _ ≫ Localization.hom P.pt (P.fst.ringMap r)
  rw [LocalizationLift.liftHom_comp]
  apply BinaryFan.IsLimit.hom_ext hP
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun b => a ≫ b) (LocalizationMaps.localizedHom_square P.fst r).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun b => b ≫ Localization.hom U r) ha).trans (baseLift_fst P hP r s).symm)))
  · exact (Category.assoc _ _ _).trans (hb.trans (baseLift_snd P hP r s).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProductLocalization
