import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointFaithfulness

/-! # Point Bundle Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The point bundle on the original abelian scheme recovers the actual Poincare test family, so its isomorphism class determines the dual point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)

def Dual.Data.DualAbelianData.poincarePointBundle_familyIso (f : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme) :
    ((D.poincarePointBundle f).pullback
      (snd (𝟙_ (Over (Spec (.of K)))) A.scheme).left).sheaf ≅ (D.poincareAt f).sheaf := by
  let T := 𝟙_ (Over (Spec (.of K)))
  have ht : toUnit (T ⊗ A.scheme) = fst T A.scheme := toUnit_unique _ _
  have hm : (lift (toUnit (T ⊗ A.scheme) ≫ f) (snd T A.scheme)).left =
      (Picard.PicardSheaf.familySchemeFunctor A.scheme).map f := by
    change (lift (toUnit (T ⊗ A.scheme) ≫ f) (snd T A.scheme)).left = (f ▷ A.scheme).left
    apply congrArg Over.Hom.left
    rw [ht]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [T, lift_fst, whiskerRight_fst]
    · simp only [T, lift_snd, whiskerRight_snd]
  exact D.poincarePointBundle_pullbackIso f (snd T A.scheme) ≪≫
    D.poincarePairDirectIso (toUnit (T ⊗ A.scheme) ≫ f) (snd T A.scheme) ≪≫
    (Scheme.Modules.pullbackCongr hm).app D.poincare.sheaf

theorem Dual.Data.DualAbelianData.poincarePointBundle_class_injective :
    Function.Injective (fun f : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme =>
      Line.Bundles.LineBundle.classOf (D.poincarePointBundle f)) := by
  intro f h he
  obtain ⟨e⟩ := Quotient.exact he
  apply D.poincareAt_class_injective (𝟙_ (Over (Spec (.of K))))
  exact Quotient.sound ⟨(D.poincarePointBundle_familyIso f).symm ≪≫
    (Scheme.Modules.pullback (snd (𝟙_ (Over (Spec (.of K)))) A.scheme).left).mapIso e ≪≫
    D.poincarePointBundle_familyIso h⟩

def Dual.Data.DualAbelianData.poincarePointBundle_oneIso :
    (D.poincarePointBundle (1 : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme)).sheaf ≅
      Line.Bundles.structureModule A.scheme.left := by
  simpa only [Dual.Data.DualAbelianData.poincarePointBundle, MonObj.comp_one] using
    D.poincarePair_one_left (𝟙 A.scheme)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
