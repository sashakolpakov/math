import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedgeAlgebra

/-! # Base Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseProduct

noncomputable section

/-! The actual principal-base divided-power comparison preserves the
native integral wedge product and its constant-one unit. -/

open _root_.CategoryTheory

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (r : R) (δR : DividedPowers (Ideal.span {r})) (I : Ideal A) (δ : DividedPowers I)
  (hI : I = Ideal.span {algebraMap R A r})
  (hδ : DividedPowers.IsDPMorphism δR δ (algebraMap R A))

theorem forms_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ p)
    (y : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ q) :
    BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ (p + q)
        (PD.DeRhamWedge.wedge R A I δ p q x y) =
      IntegralDeRham.DeRhamWedge.wedge R A p q
        (BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ p x)
        (BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ q y) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ p).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ q).mkQ_surjective y
  rw [PD.DeRhamWedge.quotient_wedge, BaseNaturality.forms_mk,
    BaseNaturality.forms_mk, BaseNaturality.forms_mk]

theorem hom_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ p)
    (y : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ q) :
    (BaseComplex.ofIdealEq R A r δR I δ hI hδ).hom.f (p + q)
        (PD.DeRhamWedge.wedge R A I δ p q x y) =
      IntegralDeRham.DeRhamWedge.wedge R A p q
        ((BaseComplex.ofIdealEq R A r δR I δ hI hδ).hom.f p x)
        ((BaseComplex.ofIdealEq R A r δR I δ hI hδ).hom.f q y) := by
  simp only [BaseNaturality.component]
  exact forms_wedge R A r δR I δ hI hδ p q x y

theorem inverse_component (n : ℕ) :
    (BaseComplex.ofIdealEq R A r δR I δ hI hδ).inv.f n =
      ModuleCat.ofHom
        ((BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ n).symm.toLinearMap.restrictScalars R) := by
  subst I
  rfl

theorem inv_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p)
    (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    (BaseComplex.ofIdealEq R A r δR I δ hI hδ).inv.f (p + q)
        (IntegralDeRham.DeRhamWedge.wedge R A p q x y) =
      PD.DeRhamWedge.wedge R A I δ p q
        ((BaseComplex.ofIdealEq R A r δR I δ hI hδ).inv.f p x)
        ((BaseComplex.ofIdealEq R A r δR I δ hI hδ).inv.f q y) := by
  simp only [inverse_component]
  apply (BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ (p + q)).injective
  change (BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ (p + q))
      ((BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ (p + q)).symm
        (IntegralDeRham.DeRhamWedge.wedge R A p q x y)) =
    (BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ (p + q))
      (PD.DeRhamWedge.wedge R A I δ p q
        ((BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ p).symm x)
        ((BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ q).symm y))
  rw [LinearEquiv.apply_symm_apply, forms_wedge,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hom_unit :
    (BaseComplex.ofIdealEq R A r δR I δ hI hδ).hom.f 0
        (PD.DeRhamWedgeAlgebra.unitForm R A I δ) = IntegralDeRham.WedgeAlgebra.unitForm R A := by
  rw [BaseNaturality.component]
  exact BaseFormCoordinates.formsEquiv_symbol R A r δR I δ hI hδ 0 1 Fin.elim0

theorem inv_unit :
    (BaseComplex.ofIdealEq R A r δR I δ hI hδ).inv.f 0
        (IntegralDeRham.WedgeAlgebra.unitForm R A) = PD.DeRhamWedgeAlgebra.unitForm R A I δ := by
  rw [inverse_component]
  apply (BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ 0).injective
  change (BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ 0)
      ((BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ 0).symm
        (IntegralDeRham.WedgeAlgebra.unitForm R A)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (BaseFormCoordinates.formsEquiv_symbol R A r δR I δ hI hδ 0 1 Fin.elim0).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseProduct
