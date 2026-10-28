import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AtIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Family Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensoring with the Poincare family does not change line-bundle Euler characteristic at ground-field points of the connected dual abelian variety. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}

theorem Dual.Data.DualAbelianData.poincareFamily_twist_euler_eq (D : Dual.Data.DualAbelianData A) (L : Line.Bundles.LineBundle A.scheme.left)
    (x y : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (pullback.fst (𝟙 (Spec (.of K))) A.scheme.hom)
      (((L.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)).tensor (D.poincareAt x)).sheaf) =
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (pullback.fst (𝟙 (Spec (.of K))) A.scheme.hom)
      (((L.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)).tensor (D.poincareAt y)).sheaf) := by
  have : IsLocallyNoetherian D.abelian.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian D.abelian.scheme.hom
  have : ConnectedSpace D.abelian.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.abelian.scheme.hom
  have hAproper : IsProper A.scheme.hom := A.proper
  have hAflat : Flat A.scheme.hom := inferInstance
  have hproper : IsProper (pullback.fst D.abelian.scheme.hom A.scheme.hom) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hAproper
  have hflat : Flat (pullback.fst D.abelian.scheme.hom A.scheme.hom) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hAflat
  let M := (L.pullback (pullback.snd D.abelian.scheme.hom A.scheme.hom)).tensor D.poincare
  let q := pullback.fst (𝟙 (Spec (.of K))) A.scheme.hom
  have e (z : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme) :
      (M.pullback ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map z)).sheaf ≅
        ((L.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)).tensor (D.poincareAt z)).sheaf :=
    Line.Bundles.LineBundle.tensorBaseChangeIso ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map z)
      (L.pullback (pullback.snd D.abelian.scheme.hom A.scheme.hom)) D.poincare ≪≫
      Tensor.ProductSheaf.tensorModuleCongr (Global.BundlePicardClass.globalBundleFamilyPullbackIso A.scheme L z) (Iso.refl _)
  have h := Rational.FiberEuler.connected_rationalFiber_euler_eq
    (X := pullback D.abelian.scheme.hom A.scheme.hom)
    (P := pullback (𝟙 (Spec (.of K))) A.scheme.hom)
    (Q := pullback (𝟙 (Spec (.of K))) A.scheme.hom)
    (f := pullback.fst D.abelian.scheme.hom A.scheme.hom)
    D.abelian.scheme.hom x.left y.left x.w y.w
    (Picard.TestFamilyPullback.familySchemeFunctor_map_isPullback A.scheme x) (Picard.TestFamilyPullback.familySchemeFunctor_map_isPullback A.scheme y) M
  exact (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso q (e x)).symm.trans
    (h.trans (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso q (e y)))

theorem Dual.Data.DualAbelianData.poincareFamily_twist_euler (D : Dual.Data.DualAbelianData A) (L : Line.Bundles.LineBundle A.scheme.left)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (pullback.fst (𝟙 (Spec (.of K))) A.scheme.hom)
      (((L.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)).tensor (D.poincareAt x)).sheaf) =
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (pullback.fst (𝟙 (Spec (.of K))) A.scheme.hom)
      (L.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)).sheaf := by
  let B := L.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)
  have e : (B.tensor (D.poincareAt (1 : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme))).sheaf ≅ B.sheaf :=
    Tensor.ProductSheaf.tensorModuleCongr (Iso.refl B.sheaf) (D.poincareAt_oneIso _) ≪≫
      Tensor.ProductSheaf.tensorModuleCommIso B.sheaf _ ≪≫ Tensor.ProductSheaf.tensorModuleUnitLeftIso B.sheaf
  exact (D.poincareFamily_twist_euler_eq L x 1).trans
    (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso _ e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
