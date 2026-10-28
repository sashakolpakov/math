import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairBilinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.PointTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality

/-! # Point Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A dual rational point gives an actual line bundle on the original abelian scheme. Its translations and inverse pairing follow from the proved Poincare bilinearity. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (f : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme)

def Dual.Data.DualAbelianData.poincarePointBundle : Line.Bundles.LineBundle A.scheme.left :=
  D.poincarePair (toUnit A.scheme ≫ f) (𝟙 A.scheme)

def Dual.Data.DualAbelianData.poincarePointBundle_pullbackIso {T : Over (Spec (.of K))} (a : T ⟶ A.scheme) :
    ((D.poincarePointBundle f).pullback a.left).sheaf ≅
      (D.poincarePair (toUnit T ≫ f) a).sheaf := by
  simpa only [Dual.Data.DualAbelianData.poincarePointBundle, comp_toUnit_assoc, Category.comp_id] using
    D.poincarePairPullbackIso (toUnit A.scheme ≫ f) (𝟙 A.scheme) a

def Dual.Data.DualAbelianData.poincarePointBundle_constantPairIso (a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    (D.poincarePair (toUnit A.scheme ≫ f) (toUnit A.scheme ≫ a)).sheaf ≅
      Line.Bundles.structureModule A.scheme.left := by
  have : Subsingleton ((𝟙_ (Over (Spec (.of K)))).left) :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  have : Nonempty ((𝟙_ (Over (Spec (.of K)))).left) :=
    inferInstanceAs (Nonempty (Spec (.of K)))
  exact (D.poincarePairPullbackIso f a (toUnit A.scheme)).symm ≪≫
    (Scheme.Modules.pullback (toUnit A.scheme).left).mapIso
      (D.poincarePair f a).trivialization_of_subsingleton ≪≫
    Line.Bundles.structureModulePullbackIso (toUnit A.scheme).left

def Dual.Data.DualAbelianData.poincarePointBundle_translationIso (a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    ((D.poincarePointBundle f).pullback (A.basePointTranslation a).left).sheaf ≅
      (D.poincarePointBundle f).sheaf :=
  D.poincarePointBundle_pullbackIso f (A.basePointTranslation a) ≪≫
    (D.poincarePair_mul_right (toUnit A.scheme ≫ f) (toUnit A.scheme ≫ a)
      (𝟙 A.scheme)).some ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (D.poincarePointBundle_constantPairIso f a) (Iso.refl _) ≪≫
    Tensor.ProductSheaf.tensorModuleUnitLeftIso (D.poincarePointBundle f).sheaf

def Dual.Data.DualAbelianData.poincarePointBundle_inversePairingIso :
    ((D.poincarePointBundle f).tensor
      ((D.poincarePointBundle f).pullback ((𝟙 A.scheme)⁻¹).left)).sheaf ≅
        Line.Bundles.structureModule A.scheme.left := by
  let h := (𝟙 A.scheme)⁻¹
  have e : (D.poincarePair (toUnit A.scheme ≫ f) 1).sheaf ≅
      ((D.poincarePair (toUnit A.scheme ≫ f) (𝟙 A.scheme)).tensor
        (D.poincarePair (toUnit A.scheme ≫ f) h)).sheaf := by
    simpa only [mul_inv_cancel] using
      (D.poincarePair_mul_right (toUnit A.scheme ≫ f) (𝟙 A.scheme) ((𝟙 A.scheme)⁻¹)).some
  exact Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (D.poincarePointBundle_pullbackIso f h) ≪≫
    e.symm ≪≫ D.poincarePair_one_right (toUnit A.scheme ≫ f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
