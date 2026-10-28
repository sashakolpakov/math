import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamIs
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealQuotientCochainProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeAlgebra

/-! # Ordinary Reduction Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction

noncomputable section

/-! Coefficient reduction preserves the native integral de Rham product
on the actual quotient complex used in good-reduction comparison. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)
  {A B : CommAlgCat.{u} R} (α : A ⟶ B)
  (hB : ∀ r, r ∈ I → algebraMap R B r = 0)

def ordinaryPairing (A : CommAlgCat.{u} R) (p q : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A).X p →ₗ[R]
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A).X q →ₗ[R]
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A).X (p + q) :=
  (IntegralDeRham.DeRhamWedge.wedge R A p q).restrictScalars₁₂ R R

def quotientPairing (A : CommAlgCat.{u} R) (p q : ℕ) :
    (Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)).X p →ₗ[R]
      (Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)).X q →ₗ[R]
        (Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)).X (p + q) :=
  IdealQuotientCochainProduct.Module.complexPairing I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)
    (ordinaryPairing R A) p q

theorem quotientPairing_mk (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p)
    (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    quotientPairing R I A p q ((I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p)).mkQ x)
        ((I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q)).mkQ y) =
      (I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A (p + q))).mkQ
        (IntegralDeRham.DeRhamWedge.wedge R A p q x y) := rfl

theorem map_mk (p : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) :
    (GeometricComparison.OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map R I α hB).f p ((I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p)).mkQ x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap α p x := rfl

theorem map_wedge (p q : ℕ)
    (x : (Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)).X p)
    (y : (Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)).X q) :
    (GeometricComparison.OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map R I α hB).f (p + q) (quotientPairing R I A p q x y) =
      IntegralDeRham.DeRhamWedge.wedge R B p q ((GeometricComparison.OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map R I α hB).f p x) ((GeometricComparison.OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map R I α hB).f q y) := by
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q)).mkQ_surjective y
  exact IntegralDeRham.WedgeNaturality.formMap_wedge α p q x y

theorem map_unit :
    (GeometricComparison.OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map R I α hB).f 0
        ((I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0)).mkQ
          (IntegralDeRham.WedgeAlgebra.unitForm R A)) = IntegralDeRham.WedgeAlgebra.unitForm R B := by
  rw [map_mk, IntegralDeRham.WedgeAlgebra.unitForm, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, map_one]
  apply congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B 1)
  funext i
  exact i.elim0

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction
