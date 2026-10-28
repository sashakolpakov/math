import OAI.NumberTheory.PadicHodge.GeometricComparison.First.ZeroQuotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendShort
import OAI.NumberTheory.PadicHodge.GeometricComparison.TriangleSaturated
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Zero Saturated Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.First.ZeroSaturatedImage.FirstZeroComplex

noncomputable section

/-! The positive Hodge image is saturated whenever the zero-term sheaf has torsion-free H-one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated

universe u v w

variable (R : Type*) [CommRing R] [IsDomain R] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasDerivedCategory.{w} C] (K : CochainComplex C ℕ) (A : C)

theorem hodge_quotient_torsionFree
    [Module.IsTorsionFree R ((DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj ((ZeroQuotient.FirstZeroComplex.complex K).extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧)] :
    Module.IsTorsionFree R
      (((DerivedCategory.singleFunctor C 0).obj A ⟶
        (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧) ⧸
      (Linear.rightComp R ((DerivedCategory.singleFunctor C 0).obj A)
        ((DerivedCategory.Q.map (HomologicalComplex.extendMap
          (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1) ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧')).range) := by
  let S := (ZeroQuotient.FirstZeroComplex.quotientSequence K).map (ComplexShape.embeddingUpNat.extendFunctor C)
  have hS : S.ShortExact := ExtendShort.ExtendShortExact.shortExact _ _ (ZeroQuotient.FirstZeroComplex.quotient_shortExact K)
  let T := (shiftFunctor (Triangle (DerivedCategory C)) (1 : ℤ)).obj
    (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang (DerivedCategory C) :=
    Triangle.shift_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) 1
  let B := (DerivedCategory.singleFunctor C 0).obj A
  let g := (DerivedCategory.Q.map (HomologicalComplex.extendMap
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1) ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧'
  have hg : T.mor₁ = -g := by
    change (1 : ℤ).negOnePow • g = -g
    rw [Int.negOnePow_one, Units.neg_smul, one_smul]
  let : Module.IsTorsionFree R (B ⟶ T.obj₃) := by
    change Module.IsTorsionFree R ((DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj ((ZeroQuotient.FirstZeroComplex.complex K).extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧)
    infer_instance
  have hrange : (Linear.rightComp R B T.mor₁).range = (Linear.rightComp R B g).range := by
    rw [hg]
    have hneg : Linear.rightComp R B (-g) = -(Linear.rightComp R B g) := by
      ext x
      exact Preadditive.comp_neg x g
    erw [hneg, LinearMap.range_neg]
    rfl
  have htf := TriangleSaturated.TriangleSaturatedImage.quotient_torsionFree R T hT B
  rw [hrange] at htf
  exact htf

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.First.ZeroSaturatedImage.FirstZeroComplex
