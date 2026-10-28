import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

/-! # Polarization Biextension Pair Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationBiextensionPairComparison

noncomputable section

/-! Comparison of the actual polarization biextension through
isomorphisms of both the abelian and dual families. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison
universe u
variable {S T : Scheme.{u}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (p : A.scheme ⟶ D.abelian.scheme) (q : B.scheme ⟶ E.abelian.scheme)
    (eA : A.scheme ≅ B.scheme) (eD : D.abelian.scheme ≅ E.abelian.scheme)
    (he : p ≫ eD.hom = eA.hom ≫ q)

include he in
theorem polarizationBiextensionMap_pairComparison (s : T ⟶ S) :
    AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap E q s ≫ (eD.inv ⊗ₘ eA.inv).left =
      ((Over.pullback s).map eA.inv ⊗ₘ (Over.pullback s).map eA.inv).left ≫
        AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s := by
  have hi : q ≫ eD.inv = eA.inv ≫ p := by
    apply (cancel_epi eA.hom).mp
    rw [← Category.assoc, ← he]
    simp only [Category.assoc, eD.hom_inv_id, Category.comp_id, eA.hom_inv_id_assoc]
  have hiL := congrArg Over.Hom.left hi
  simp only [Over.comp_left] at hiL
  let X := (B.pullback s).scheme
  let Y := (A.pullback s).scheme
  let a : X.left ⟶ Y.left := ((Over.pullback s).map eA.inv).left
  let a₂ : (X ⊗ X).left ⟶ (Y ⊗ Y).left :=
    ((Over.pullback s).map eA.inv ⊗ₘ (Over.pullback s).map eA.inv).left
  let b : X.left ⟶ B.scheme.left := pullback.fst B.scheme.hom s
  let c : Y.left ⟶ A.scheme.left := pullback.fst A.scheme.hom s
  have hac : a ≫ c = b ≫ eA.inv.left := AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst eA.inv s
  apply Over.tensorObj_ext
  · have hrf : (eD.inv ⊗ₘ eA.inv).left ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst E.abelian.scheme.hom B.scheme.hom ≫ eD.inv.left := Over.tensorHom_left_fst _ _ _ _
    have hqf : AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap E q s ≫ pullback.fst E.abelian.scheme.hom B.scheme.hom =
        pullback.fst X.hom X.hom ≫ b ≫ q.left := AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_fst E q s
    have htf : AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst Y.hom Y.hom ≫ c ≫ p.left := AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_fst D p s
    have haf : a₂ ≫ pullback.fst Y.hom Y.hom = pullback.fst X.hom X.hom ≫ a :=
      Over.tensorHom_left_fst _ _ _ _
    change _ = (a₂ ≫ AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s) ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom
    simp only [Category.assoc, hrf, reassoc_of% hqf, hiL, htf,
      reassoc_of% haf, reassoc_of% hac]
  · have hrs : (eD.inv ⊗ₘ eA.inv).left ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd E.abelian.scheme.hom B.scheme.hom ≫ eA.inv.left := Over.tensorHom_left_snd _ _ _ _
    have hqs : AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap E q s ≫ pullback.snd E.abelian.scheme.hom B.scheme.hom =
        pullback.snd X.hom X.hom ≫ b := AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_snd E q s
    have hts : AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd Y.hom Y.hom ≫ c := AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_snd D p s
    have has : a₂ ≫ pullback.snd Y.hom Y.hom = pullback.snd X.hom X.hom ≫ a :=
      Over.tensorHom_left_snd _ _ _ _
    change _ = (a₂ ≫ AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s) ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom
    simp only [Category.assoc, hrs, reassoc_of% hqs, hts, reassoc_of% has, hac]

def polarizationBiextensionPairIso
    (hP : E.poincare.sheaf ≅ (D.poincare.pullback (eD.inv ⊗ₘ eA.inv).left).sheaf)
    (s : T ⟶ S) :
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt E q s).sheaf ≅
      ((AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s).pullback
        ((Over.pullback s).map eA.inv ⊗ₘ (Over.pullback s).map eA.inv).left).sheaf :=
  (Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap E q s)).mapIso hP ≪≫
  (Scheme.Modules.pullbackComp (AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap E q s)
    (eD.inv ⊗ₘ eA.inv).left).app D.poincare.sheaf ≪≫
  (Scheme.Modules.pullbackCongr (polarizationBiextensionMap_pairComparison D E p q eA eD he s)).app
    D.poincare.sheaf ≪≫
  (Scheme.Modules.pullbackComp
    ((Over.pullback s).map eA.inv ⊗ₘ (Over.pullback s).map eA.inv).left
    (AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s)).symm.app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationBiextensionPairComparison
