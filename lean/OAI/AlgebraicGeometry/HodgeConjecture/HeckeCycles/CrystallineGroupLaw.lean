import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingAdditivity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineProductIdentity

/-! # Crystalline Group Law -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineGroupLaw.CM

noncomputable section

/-! The complete GeometricComparison prerequisite on the actual product model proves
the group-law formula on all crystalline H1. The two axis endomorphisms
extend; their proved Betti relation transfers to crystalline cohomology,
and composition with the first projection recovers multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingAdditivity.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

def identityEnd : A.ExtendingEndomorphism where
  generic := 1
  integral := 1
  compatible := by
    let fi : A.localFiber.scheme ⟶ A.localFiber.scheme :=
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map (𝟙 A.integral.scheme)
    let fg : (A.variety.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).scheme ⟶
        (A.variety.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).scheme :=
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map (𝟙 A.variety.scheme)
    have hi : fi = 𝟙 A.localFiber.scheme :=
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map_id A.integral.scheme
    have hg : fg = 𝟙 (A.variety.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).scheme :=
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map_id A.variety.scheme
    change fi ≫ A.genericIso.hom = A.genericIso.hom ≫ fg
    exact (congrArg (· ≫ A.genericIso.hom) hi).trans
      ((Category.id_comp A.genericIso.hom).trans
        ((Category.comp_id A.genericIso.hom).symm.trans
          (congrArg (A.genericIso.hom ≫ ·) hg.symm)))

def scalarRealization : A.HeckeRealization ℚ where
  action := Algebra.ofId ℚ (FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A.variety.scheme)
  presentation r := Finsupp.single (identityEnd A) r
  represents r := by
    classical
    simp only [Finsupp.sum_single_index, TensorProduct.zero_tmul]
    rfl

def AxisRelation : Prop :=
  let b := NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
  NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q ((Over.pullback b).map (ProductEndomorphisms.CM.fold A.integral.scheme)) =
    NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q ((Over.pullback b).map (ProductEndomorphisms.CM.left A.integral.scheme)) +
      NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q ((Over.pullback b).map (ProductEndomorphisms.CM.right A.integral.scheme))

theorem axisRelation_of_additivity
    (h : (ProductComparisonModel.CM.productModel A).crystallinePullback
        (ExtendingAdditivity.CM.addEnd (ProductComparisonModel.CM.productModel A) (ProductComparisonModel.CM.leftEnd A) (ProductComparisonModel.CM.rightEnd A)) =
      (ProductComparisonModel.CM.productModel A).crystallinePullback (ProductComparisonModel.CM.leftEnd A) +
        (ProductComparisonModel.CM.productModel A).crystallinePullback (ProductComparisonModel.CM.rightEnd A)) : AxisRelation A := h

theorem axisRelation_from_full_GeometricComparison
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = iota.comp κ)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    AxisRelation A := by
  apply axisRelation_of_additivity A
  exact ExtendingAdditivity.CM.crystalline_addEnd_of_full_comparison (ProductComparisonModel.CM.productModel A) κ jComplex iota
    (scalarRealization (ProductComparisonModel.CM.productModel A)) (ProductComparisonModel.CM.productProjectivePresentation A (jComplex.comp κ) P) ℓ
    (hGeometricComparison K q κ jComplex iota jq hplace (ProductComparisonModel.CM.productModel A) ℚ (scalarRealization (ProductComparisonModel.CM.productModel A))
      (ProductComparisonModel.CM.productProjectivePresentation A (jComplex.comp κ) P) ℓ hℓq) (ProductComparisonModel.CM.leftEnd A) (ProductComparisonModel.CM.rightEnd A)

theorem groupLaw_from_full_GeometricComparison
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = iota.comp κ)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    CrystallineMonoidAction.CM.End.GroupLawIdentity q A.specialFiber.scheme :=
  CrystallineProductIdentity.CM.groupLaw_of_axis_identity q A.integral.scheme
    (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))
    (axisRelation_from_full_GeometricComparison A hGeometricComparison κ jComplex iota hplace P ℓ hℓq)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineGroupLaw.CM
