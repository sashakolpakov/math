import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuotientTotalImage

/-! # Quotient Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection

noncomputable section

/-! The original quotient-of-total comparison sends coefficient
reduction to pointwise reduction of the original Cech presheaf complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v
variable (R : Type) [CommRing R] (I : Ideal R)
  {C : Type u} [Category.{v} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} R) ℕ)

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E K

def complex : K ⟶ CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex Q K where
  f q := Functor.whiskerLeft (K.X q) (IntegralComparison.Module.IdealQuotient.projection R I)
  comm' q r _ := by
    apply NatTrans.ext
    funext W
    exact ((IntegralComparison.Module.IdealQuotient.projection R I).naturality ((K.d q r).app W)).symm

def bicomplex := ((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).map (complex R I K)

theorem bicomplex_coordinates : QuotientTotalImage.QuotientBicomplexProjection.bicomplex R I B ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso Q E hE K).hom = bicomplex R I E K := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply HomologicalComplex.Hom.ext
  funext r
  change (IntegralComparison.Module.IdealQuotient.projection R I).app _ ≫
      (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso Q E hE (K.X q)).hom.f r =
    Limits.Pi.map (fun i : (E.obj (op ⦋r⦌)).I =>
      (IntegralComparison.Module.IdealQuotient.projection R I).app ((K.X q).obj (op ((E.obj (op ⦋r⦌)).obj i))))
  rw [GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  apply Pi.hom_ext
  intro i
  erw [Category.assoc, piComparison_comp_π, Pi.map_π]
  exact ((IntegralComparison.Module.IdealQuotient.projection R I).naturality
    (Pi.π (fun j : (E.obj (op ⦋r⦌)).I => (K.X q).obj (op ((E.obj (op ⦋r⦌)).obj j))) i)).symm

def map := HomologicalComplex₂.total.map (bicomplex R I E K) (.up ℕ)

theorem total : IntegralComparison.Module.IdealQuotient.complexProjection R I ((B).total (.up ℕ)) ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.totalIso Q E hE K).hom = CechPresheafQuotientProjection.map R I E K :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ HomologicalComplex₂.total.map
      (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso Q E hE K).hom (.up ℕ))
        (QuotientTotalImage.QuotientBicomplexProjection.inverse R I B)).trans
      ((HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).symm.trans
        (congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex_coordinates R I E hE K))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection
