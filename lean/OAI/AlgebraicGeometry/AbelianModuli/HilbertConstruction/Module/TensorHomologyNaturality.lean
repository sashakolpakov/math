import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ModuleTensorHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.CochainBicomplex

/-! # Tensor Homology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor

noncomputable section

/-! The tensor-homology comparison is natural in both a flat tensor factor and the cochain complex. These are the compatibility laws used by varying affine parameter rings. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u

variable {R : Type u} [CommRing R]
variable {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

def scalarMap (a : A →ₗ[R] B) : TensorFunctor.ModuleTensorFunctor.tensor (R := R) A ⟶ TensorFunctor.ModuleTensorFunctor.tensor (R := R) B where
  app M := ModuleCat.ofHom (a.rTensor M)
  naturality M N f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

theorem flatHomologyIso_scalar_naturality [Module.Flat R A] [Module.Flat R B]
    (a : A →ₗ[R] B) (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (scalarMap a).app (C.homology n) ≫ (HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor.flatHomologyIso B C n).hom =
      (HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor.flatHomologyIso A C n).hom ≫
        HomologicalComplex.homologyMap (Tensor.CochainBicomplex.tensorCochainMap C (ModuleCat.ofHom a)) n := by
  change (scalarMap a).app ((C.sc n).homology) ≫ ((C.sc n).mapHomologyIso (TensorFunctor.ModuleTensorFunctor.tensor B)).inv =
    ((C.sc n).mapHomologyIso (TensorFunctor.ModuleTensorFunctor.tensor A)).inv ≫
      ShortComplex.homologyMap ((C.sc n).mapNatTrans (scalarMap a))
  rw [ShortComplex.homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]

theorem flatHomologyIso_complex_naturality [Module.Flat R A]
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (a : C ⟶ D) (n : ℕ) :
    (TensorFunctor.ModuleTensorFunctor.tensor A).map (HomologicalComplex.homologyMap a n) ≫ (HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor.flatHomologyIso A D n).hom =
      (HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor.flatHomologyIso A C n).hom ≫ HomologicalComplex.homologyMap (TensorFunctor.ModuleTensorFunctor.map A a) n :=
  ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map a) (TensorFunctor.ModuleTensorFunctor.tensor A)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorHomologyNaturality.ModuleTensorFunctor
