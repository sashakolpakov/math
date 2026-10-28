import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.Quotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendShort
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # One Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.OneEquivalence.FirstThreeComplex

noncomputable section

/-! Retaining the first three terms preserves the actual degree-one derived sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (K : CochainComplex C ℕ) (A : C)

theorem hone_bijective :
    Function.Bijective
      (fun x : (DerivedCategory.singleFunctor C 0).obj A ⟶
          (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧ =>
        x ≫ (DerivedCategory.Q.map
          (HomologicalComplex.extendMap (ThreeComplex.FirstThreeComplex.projection K) ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧') := by
  let S := (Quotient.FirstThreeComplex.quotientSequence K).map (ComplexShape.embeddingUpNat.extendFunctor C)
  have hS : S.ShortExact := ExtendShort.ExtendShortExact.shortExact _ _ (Quotient.FirstThreeComplex.quotient_shortExact K)
  let T := (shiftFunctor (Triangle (DerivedCategory C)) (1 : ℤ)).obj
    (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang (DerivedCategory C) :=
    Triangle.shift_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) 1
  let L : CochainComplex C ℤ :=
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K 3).extend ComplexShape.embeddingUpNat
  let : L.IsStrictlyGE 3 := TruncationBoundsGE.TruncationBounds.extended_isStrictlyGE K 3
  let : (DerivedCategory.Q.obj L).IsGE 3 := inferInstance
  let : ((DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧).IsGE 2 :=
    DerivedCategory.TStructure.t.isGE_shift _ 3 1 2 (by omega)
  let : DerivedCategory.TStructure.t.IsGE T.obj₁ 2 := by
    change ((DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧).IsGE 2
    infer_instance
  let : DerivedCategory.TStructure.t.IsGE (T.obj₁⟦(1 : ℤ)⟧) 1 :=
    DerivedCategory.TStructure.t.isGE_shift _ 2 1 1 (by omega)
  constructor
  · intro x y hxy
    dsimp only at hxy
    have hz : (x - y) ≫ T.mor₂ = 0 := by
      change (x - y) ≫ ((1 : ℤ).negOnePow • (DerivedCategory.Q.map
        (HomologicalComplex.extendMap (ThreeComplex.FirstThreeComplex.projection K) ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧') = 0
      rw [Int.negOnePow_one, Units.neg_smul, one_smul]
      rw [Preadditive.comp_neg, Preadditive.sub_comp, hxy, sub_self, neg_zero]
    obtain ⟨z, hz⟩ := T.coyoneda_exact₂ hT (x - y) hz
    have hzero : z = 0 := DerivedCategory.TStructure.t.zero z 0 2 (by omega)
    apply sub_eq_zero.mp
    rw [hz, hzero, zero_comp]
    rfl
  · intro y
    have hy : y ≫ T.mor₃ = 0 := DerivedCategory.TStructure.t.zero _ 0 1 (by omega)
    obtain ⟨x, hx⟩ := T.coyoneda_exact₃ hT y hy
    let x' : (DerivedCategory.singleFunctor C 0).obj A ⟶
        (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧ := x
    refine ⟨-x', ?_⟩
    change y = x' ≫ ((1 : ℤ).negOnePow • (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (ThreeComplex.FirstThreeComplex.projection K) ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧') at hx
    rw [Int.negOnePow_one, Units.neg_smul, one_smul] at hx
    rw [Preadditive.comp_neg] at hx
    dsimp only
    rw [Preadditive.neg_comp]
    exact hx.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.OneEquivalence.FirstThreeComplex
