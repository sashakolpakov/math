import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap

/-! # Scalar Wedge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.ScalarWedge

noncomputable section

/-! The actual change-of-base map on differential symbols preserves
the integral wedge product in every degree. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange

universe u
variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

theorem extension_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B (p+q) (DeRhamWedge.wedge R A p q x y) =
      DeRhamWedge.wedge S B p q
        (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B p x) (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B q y) := by
  let L : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B (p+q) :=
    ((DeRhamWedge.wedge R A p q).restrictScalars₁₂ R R).compr₂
      (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B (p+q))
  let D : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B (p+q) :=
    ((DeRhamWedge.wedge S B p q).restrictScalars₁₂ R R).compl₁₂
      (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B p) (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B q)
  have h : L = D := by
    apply RationalDeRham.Leibniz.Wedge.linearMap_ext_symbols R A p
    intro a v
    apply RationalDeRham.Leibniz.Wedge.linearMap_ext_symbols R A q
    intro b w
    change GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B (p+q)
        (DeRhamWedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) =
      DeRhamWedge.wedge S B p q
        (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
        (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w))
    rw [DeRhamWedge.wedge_symbol, GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap_symbol,
      GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap_symbol, GeometricComparison.Forms.ScalarMap.FormsBaseChange.formExtensionMap_symbol,
      DeRhamWedge.wedge_symbol, map_mul]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

theorem scalar_one_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B (p+q) ((1 : S) ⊗ₜ[R] DeRhamWedge.wedge R A p q x y) =
      DeRhamWedge.wedge S B p q
        (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B p ((1 : S) ⊗ₜ[R] x))
        (GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B q ((1 : S) ⊗ₜ[R] y)) := by
  simp only [GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap_tmul, one_smul]
  exact extension_wedge R S A B p q x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.ScalarWedge
