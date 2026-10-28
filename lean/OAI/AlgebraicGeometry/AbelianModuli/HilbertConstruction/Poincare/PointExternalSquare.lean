import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle

/-! # Point External Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Addition on an abelian scheme has an actual section. The pullback of a Poincare point bundle by addition is its external tensor square. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem Abelian.Schemes.AbelianScheme.addition_section {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) :
    lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme) ≫
      (fst A.scheme A.scheme * snd A.scheme A.scheme) = 𝟙 A.scheme := by
  rw [MonObj.comp_mul, lift_fst, lift_snd, mul_one]

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)

def Dual.Data.DualAbelianData.poincarePointBundle_additionIso (f : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme) :
    ((D.poincarePointBundle f).pullback
      (fst A.scheme A.scheme * snd A.scheme A.scheme).left).sheaf ≅
    (Graph.ExternalTensorBundle.externalTensorBundle (A := A.scheme) (B := A.scheme)
      (D.poincarePointBundle f) (D.poincarePointBundle f)).sheaf :=
  D.poincarePointBundle_pullbackIso f (fst A.scheme A.scheme * snd A.scheme A.scheme) ≪≫
    (D.poincarePair_mul_right (toUnit (A.scheme ⊗ A.scheme) ≫ f)
      (fst A.scheme A.scheme) (snd A.scheme A.scheme)).some ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (D.poincarePointBundle_pullbackIso f (fst A.scheme A.scheme)).symm
      (D.poincarePointBundle_pullbackIso f (snd A.scheme A.scheme)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
