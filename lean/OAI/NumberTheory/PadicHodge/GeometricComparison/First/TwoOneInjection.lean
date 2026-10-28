import OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoQuotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendShort
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Two One Injection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoOneInjection.FirstTwoComplex

noncomputable section

/-! The native projection retaining degrees zero and one is injective on degree-one derived sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (K : CochainComplex C ℕ) (A : C)

theorem hone_injective :
    Function.Injective
      (fun x : (DerivedCategory.singleFunctor C 0).obj A ⟶
          (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧ =>
        x ≫ (DerivedCategory.Q.map
          (HomologicalComplex.extendMap (TwoComplex.FirstTwoComplex.projection K) ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧') := by
  let S := (TwoQuotient.FirstTwoComplex.quotientSequence K).map (ComplexShape.embeddingUpNat.extendFunctor C)
  have hS : S.ShortExact := ExtendShort.ExtendShortExact.shortExact _ _ (TwoQuotient.FirstTwoComplex.quotient_shortExact K)
  let T := (shiftFunctor (Triangle (DerivedCategory C)) (1 : ℤ)).obj
    (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang (DerivedCategory C) :=
    Triangle.shift_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) 1
  let L : CochainComplex C ℤ :=
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K 2).extend ComplexShape.embeddingUpNat
  let : L.IsStrictlyGE 2 := TruncationBoundsGE.TruncationBounds.extended_isStrictlyGE K 2
  let : (DerivedCategory.Q.obj L).IsGE 2 := inferInstance
  let : ((DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧).IsGE 1 :=
    DerivedCategory.TStructure.t.isGE_shift _ 2 1 1 (by omega)
  let : DerivedCategory.TStructure.t.IsGE T.obj₁ 1 := by
    change ((DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧).IsGE 1
    infer_instance
  intro x y hxy
  dsimp only at hxy
  have hz : (x - y) ≫ T.mor₂ = 0 := by
    change (x - y) ≫ ((1 : ℤ).negOnePow • (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (TwoComplex.FirstTwoComplex.projection K) ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧') = 0
    rw [Int.negOnePow_one, Units.neg_smul, one_smul]
    rw [Preadditive.comp_neg, Preadditive.sub_comp, hxy, sub_self, neg_zero]
  obtain ⟨z, hz⟩ := T.coyoneda_exact₂ hT (x - y) hz
  have hzero : z = 0 := DerivedCategory.TStructure.t.zero z 0 1 (by omega)
  apply sub_eq_zero.mp
  rw [hz, hzero, zero_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoOneInjection.FirstTwoComplex
