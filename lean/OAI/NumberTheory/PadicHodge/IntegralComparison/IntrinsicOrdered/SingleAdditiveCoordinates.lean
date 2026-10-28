import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.MappedSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.FunctorSingleCoordinates

/-! # Single Additive Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic

noncomputable section

/-! The actual native additive total isomorphism preserves the
original ordered single-degree coordinate, including the coefficient
comparison on ordinary Čech cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

abbrev scalars := CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)
abbrev linearFunctor := AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π ⋙
  OrderedCech.Functor.Projection.functor U
abbrev additiveFunctor := Relative.AdditiveCechConcentration.presheaves (X := X) ⋙
  OrderedCech.Functor.Projection.functor U

def coefficientFunctorIso :
    IntegralComparison.Functor.SingleCoefficientChange.mappedFunctor (linearFunctor π U) (scalars (S := S)) ≅
      additiveFunctor U :=
  NatIso.ofComponents (fun N => OrderedCech.CoefficientChange.complexIso U (scalars (S := S))
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π N)) (by
      intro M N a
      exact OrderedCech.CoefficientChange.naturality U (scalars (S := S))
        (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M) ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map a))

variable (N : X.Modules) (c g : ℕ)

abbrev singleCoefficient := (single X.Modules (.up ℕ) c).obj N

def coefficientIso :=
  (scalars (S := S)).mapIso (homologyMapIso (CechCoordinates.Intrinsic.iso π U N).symm g) ≪≫
    IntegralComparison.Functor.SingleCoefficientIso.coefficientIso (linearFunctor π U) (scalars (S := S))
      (additiveFunctor U) (coefficientFunctorIso π U) N g

private theorem coefficient_total_iso :
    OrderedCech.CoefficientTotal.totalIso U (scalars (S := S))
      (RelativeCech.CoefficientQuasiIso.coefficients π (singleCoefficient N c)) =
    IntegralComparison.Functor.SingleCoefficientIso.totalIso (linearFunctor π U) (scalars (S := S))
      (additiveFunctor U) (coefficientFunctorIso π U) N c := by
  rfl

private theorem homology_transport :
    ((((Cech.ConcentrationNaturality.totalFunctor π U).obj (singleCoefficient N c)).sc (g+c)).mapHomologyIso
      (scalars (S := S))).inv ≫
      homologyMap (((scalars (S := S)).mapHomologicalComplex (.up ℕ)).map
        (CechTotalCoordinates.Intrinsic.iso π U (singleCoefficient N c)).inv) (g+c) =
    (scalars (S := S)).map (homologyMap
      (CechTotalCoordinates.Intrinsic.iso π U (singleCoefficient N c)).inv (g+c)) ≫
      ((((CechTotalCoordinates.Intrinsic.sourceFunctor π U).obj (singleCoefficient N c)).sc (g+c)).mapHomologyIso
        (scalars (S := S))).inv := by
  let a := (CechTotalCoordinates.Intrinsic.iso π U (singleCoefficient N c)).inv
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) (g+c)).map a) (scalars (S := S))
  have hi := CohomologyConcentrationNaturality.inverse_square _ _
    ((((Cech.ConcentrationNaturality.totalFunctor π U).obj (singleCoefficient N c)).sc (g+c)).mapHomologyIso
      (scalars (S := S)))
    ((((CechTotalCoordinates.Intrinsic.sourceFunctor π U).obj (singleCoefficient N c)).sc (g+c)).mapHomologyIso
      (scalars (S := S))) h
  exact hi.symm

theorem native_factor :
    (CechAdditiveCoordinates.Intrinsic.homologyIso π U (singleCoefficient N c) (g+c)).hom =
      (scalars (S := S)).map (homologyMap
        (CechTotalCoordinates.Intrinsic.iso π U (singleCoefficient N c)).inv (g+c)) ≫
      (IntegralComparison.Functor.SingleCoefficientIso.homologyIso (linearFunctor π U) (scalars (S := S))
        (additiveFunctor U) (coefficientFunctorIso π U) N c g).hom := by
  have h := GeometricComparison.ExactHomology.ExactHomologyComparison.naturality (scalars (S := S)) (.up ℕ)
    (CechAdditiveCoordinates.Intrinsic.totalIso π U (singleCoefficient N c))
    (IntegralComparison.Functor.SingleCoefficientIso.totalIso (linearFunctor π U) (scalars (S := S))
      (additiveFunctor U) (coefficientFunctorIso π U) N c)
    (CechTotalCoordinates.Intrinsic.iso π U (singleCoefficient N c)).inv
    (𝟙 _) (by
      rw [Category.comp_id, ← coefficient_total_iso]
      rfl) (g+c)
  simp only [GeometricComparison.ExactHomology.ExactHomologyComparison.iso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, homologyFunctor_map, homologyMap_id, Category.comp_id] at h
  simpa only [CechAdditiveCoordinates.Intrinsic.homologyIso,
    IntegralComparison.Functor.SingleCoefficientIso.homologyIso, Iso.trans_hom, Iso.symm_hom,
    homologyMapIso_hom] using h.symm

theorem linear_inverse :
    homologyMap (CechTotalCoordinates.Intrinsic.iso π U (singleCoefficient N c)).inv (g+c) ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (linearFunctor π U) N c g).hom =
    (IntegralComparison.Functor.SingleTotal.homologyIso (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U) N c g).hom ≫
      homologyMap (CechCoordinates.Intrinsic.iso π U N).inv g :=
  IntegralComparison.Functor.SingleMapCoordinates.naturality (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U)
    (linearFunctor π U) (CechCoordinates.Intrinsic.functorIso π U).inv N c g

theorem comparison :
    (CechAdditiveCoordinates.Intrinsic.homologyIso π U (singleCoefficient N c) (g+c)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (additiveFunctor U) N c g).hom =
    (scalars (S := S)).map (OrderedCech.CechSingle.homologyIso π U N c g).hom ≫
      (coefficientIso π U N g).hom := by
  have hl := congrArg (scalars (S := S)).map (linear_inverse π U N c g)
  simp only [Functor.map_comp] at hl
  rw [native_factor, Category.assoc, IntegralComparison.Functor.SingleCoefficientIso.comparison]
  rw [← Category.assoc, hl]
  rw [OrderedCech.FunctorSingleCoordinates.homologyIso_eq]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic
