import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechAcyclic
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.OneEquivalence

/-! # De Rham One Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamOneCech.IntegralDeRhamHOneCech

noncomputable section

/-! The original integral de Rham H-one is computed by the finite affine Čech resolution of its first three terms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X

local instance : HasExt.{1} V := HasExt.standard _

def projection : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1 →ₗ[R]
    ((DerivedCategory.singleFunctor V 0).obj A ⟶
      (DerivedCategory.Q.obj ((K).extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧) where
  toFun x := x ≫ (DerivedCategory.Q.map
    (HomologicalComplex.extendMap (FirstThree.ThreeComplex.FirstThreeComplex.projection (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))
      ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧'
  map_add' x y := Preadditive.add_comp _ _ _ x y _
  map_smul' r x := Linear.smul_comp _ _ _ r x _

def projectionEquiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1 ≃ₗ[R]
    ((DerivedCategory.singleFunctor V 0).obj A ⟶
      (DerivedCategory.Q.obj ((K).extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧) :=
  LinearEquiv.ofBijective (projection R X)
    (FirstThree.OneEquivalence.FirstThreeComplex.hone_bijective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) A)

variable [Module.Flat ℤ R] [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

def sections : CochainComplex (ModuleCat.{0} R) ℤ := IntrinsicCech.Terms.IntrinsicCechComparison.sections R X.left U K

def equiv : (sections R X U).homology 1 ≃ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1 :=
  (IntrinsicCech.Terms.IntrinsicCechComparison.equiv R X.left U hcover K
    (IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic.integerTotal_ext_subsingleton R X U hU) 1).trans
      (projectionEquiv R X).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamOneCech.IntegralDeRhamHOneCech
