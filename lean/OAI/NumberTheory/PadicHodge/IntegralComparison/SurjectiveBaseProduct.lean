import OAI.NumberTheory.PadicHodge.GeometricComparison.SurjectiveBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeAlgebra

/-! # Surjective Base Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveBaseProduct

noncomputable section

/-! The genuine ordinary de Rham comparison for a surjective base
map preserves the integral wedge product and the constant-one form. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
universe u
variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  (h : Function.Surjective (algebraMap R S))

theorem forms_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h (p+q)
      (IntegralDeRham.DeRhamWedge.wedge R A p q x y) =
    IntegralDeRham.DeRhamWedge.wedge S A p q
      (OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h p x)
      (OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h q y) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A p).mkQ_surjective x
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | single v a =>
    obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A q).mkQ_surjective y
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
    | single w b =>
      change OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h (p+q)
        (IntegralDeRham.DeRhamWedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) =
          IntegralDeRham.DeRhamWedge.wedge S A p q
            (OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
            (OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w))
      rw [IntegralDeRham.DeRhamWedge.wedge_symbol, OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol,
        OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol, OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol,
        IntegralDeRham.DeRhamWedge.wedge_symbol]

theorem hom_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    (GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso R S A h).hom.f (p+q)
      (IntegralDeRham.DeRhamWedge.wedge R A p q x y) =
    IntegralDeRham.DeRhamWedge.wedge S A p q
      ((GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso R S A h).hom.f p x)
      ((GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso R S A h).hom.f q y) :=
  forms_wedge R S A h p q x y

theorem hom_unit : (GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso R S A h).hom.f 0
    (IntegralDeRham.WedgeAlgebra.unitForm R A) = IntegralDeRham.WedgeAlgebra.unitForm S A :=
  OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol R S A h 0 1 Fin.elim0

theorem inv_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A q) :
    (GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso R S A h).inv.f (p+q)
      (IntegralDeRham.DeRhamWedge.wedge S A p q x y) =
    IntegralDeRham.DeRhamWedge.wedge R A p q
      ((GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso R S A h).inv.f p x)
      ((GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso R S A h).inv.f q y) := by
  apply (OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h (p+q)).injective
  change OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h (p+q)
    ((OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h (p+q)).symm
      (IntegralDeRham.DeRhamWedge.wedge S A p q x y)) =
      OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h (p+q)
        (IntegralDeRham.DeRhamWedge.wedge R A p q
          ((OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h p).symm x)
          ((OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h q).symm y))
  rw [LinearEquiv.apply_symm_apply, forms_wedge,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveBaseProduct
