import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.LocalDescentGluing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.IntrinsicCompatibleBaseChange

/-! # Open Descent Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenDescentComparison.PicardOpenDescentComparison

noncomputable section

/-! Transporting a descent computed in native pullback frames to the
open-restriction comparison used for global gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf.PicardModuleHomSheaf

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares

theorem transport_square {C : Type*} [Category C]
    {M N P Q M' N' P' Q' : C}
    (a : M ⟶ N) (b : P ⟶ Q) (s : M ≅ P) (t : N ≅ Q)
    (eM : M' ≅ M) (eN : N' ≅ N) (eP : P' ≅ P) (eQ : Q' ≅ Q)
    (h : a ≫ t.hom = s.hom ≫ b) :
    (eM.hom ≫ a ≫ eN.inv) ≫ (eN ≪≫ t ≪≫ eQ.symm).hom =
      (eM ≪≫ s ≪≫ eP.symm).hom ≫ (eP.hom ≫ b ≫ eQ.inv) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc a t.hom, h, Category.assoc]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

def relativeComparisonIso (M : Y.Modules) :
    (Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι) ≅
      ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι :=
  (Scheme.Modules.pullback (f ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) ≪≫
    (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) (morphismRestrict_ι f U).symm).symm.app M ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app
      ((Scheme.Modules.pullback f).obj M)).symm

theorem relativeComparison_eq (M : Y.Modules) :
    relativeComparisonIso f U M = (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U).symm.app M := by
  apply Iso.ext
  dsimp only [relativeComparisonIso, Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso, NormalizedSquares.PicardNormalizedSquares.sectionSquareIso]
  rfl

def restrictedMorphism {M N : Y.Modules}
    (a : (Scheme.Modules.pullback U.ι).obj M ⟶ (Scheme.Modules.pullback U.ι).obj N) :
    M.restrict U.ι ⟶ N.restrict U.ι :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M ≫ a ≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app N

theorem descent_square_of_native {M N : Y.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (a : (Scheme.Modules.pullback U.ι).obj M ⟶ (Scheme.Modules.pullback U.ι).obj N)
    (ha : (Scheme.Modules.pullback (f ∣_ U)).map a =
      (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) (morphismRestrict_ι f U).symm).inv.app M ≫
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map q ≫
          (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) (morphismRestrict_ι f U).symm).hom.app N) :
    (Scheme.Modules.pullback (f ∣_ U)).map (restrictedMorphism U a) ≫
        (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U).inv.app N =
      (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U).inv.app M ≫
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map q := by
  let Lg := Scheme.Modules.pullback (f ∣_ U)
  let Li := Scheme.Modules.pullback (f ⁻¹ᵁ U).ι
  let R := Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let α := NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) (morphismRestrict_ι f U).symm
  let β := Scheme.Modules.restrictFunctorIsoPullback U.ι
  let γ := Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι
  let eM := Lg.mapIso (β.app M)
  let eN := Lg.mapIso (β.app N)
  let eP := γ.app ((Scheme.Modules.pullback f).obj M)
  let eQ := γ.app ((Scheme.Modules.pullback f).obj N)
  have hn : α.hom.app N ≫ α.inv.app N = 𝟙 _ := (α.app N).hom_inv_id
  have hs : Lg.map a ≫ (α.app N).inv = (α.app M).inv ≫ Li.map q := by
    change Lg.map a ≫ α.inv.app N = α.inv.app M ≫ Li.map q
    rw [ha]
    simp only [Category.assoc]
    rw [hn]
    exact congrArg (fun r ↦ α.inv.app M ≫ r) (Category.comp_id (Li.map q))
  have hq : eP.hom ≫ Li.map q ≫ eQ.inv = R.map q := by
    have hg : Li.map q ≫ γ.inv.app ((Scheme.Modules.pullback f).obj N) =
        γ.inv.app ((Scheme.Modules.pullback f).obj M) ≫ R.map q := γ.inv.naturality q
    change γ.hom.app ((Scheme.Modules.pullback f).obj M) ≫
      Li.map q ≫ γ.inv.app ((Scheme.Modules.pullback f).obj N) = R.map q
    rw [hg]
    exact (γ.app ((Scheme.Modules.pullback f).obj M)).hom_inv_id_assoc _
  have hc : Lg.map (restrictedMorphism U a) = eM.hom ≫ Lg.map a ≫ eN.inv := by
    exact (Lg.map_comp _ _).trans (congrArg (fun r ↦ Lg.map (β.hom.app M) ≫ r) (Lg.map_comp _ _))
  have ht := transport_square (Lg.map a) (Li.map q) (α.app M).symm (α.app N).symm
    eM eN eP eQ hs
  have hM : (eM ≪≫ (α.app M).symm ≪≫ eP.symm).hom =
      (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U).inv.app M :=
    congrArg Iso.hom (relativeComparison_eq f U M)
  have hN : (eN ≪≫ (α.app N).symm ≪≫ eQ.symm).hom =
      (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U).inv.app N :=
    congrArg Iso.hom (relativeComparison_eq f U N)
  exact (congrArg₂ (fun r s ↦ r ≫ s) hc hN.symm).trans
    (ht.trans (congrArg₂ (fun r s ↦ r ≫ s) hM hq))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenDescentComparison.PicardOpenDescentComparison
