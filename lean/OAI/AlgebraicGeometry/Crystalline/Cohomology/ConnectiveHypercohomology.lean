import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeLayer
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendShort
import OAI.NumberTheory.PadicHodge.GeometricComparison.TriangleFinitenessFinite
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Connective Hypercohomology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ConnectiveHypercohomology.ConnectiveHypercohomologyFiniteness

noncomputable section

/-! # All-degree hypercohomology finiteness from finite coefficient Ext of the terms -/

open _root_.CategoryTheory Limits Pretriangulated

universe u v w z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasDerivedCategory.{z} C]
  (R : Type t) [CommRing R] [IsNoetherianRing R] [Linear R C] (A : C) (K : CochainComplex C ℕ)

theorem tail_finite (n : ℕ)
    (hterms : ∀ r, r ≤ n → Module.Finite R (Abelian.Ext.{w} A (K.X r) (n - r)))
    (r : ℕ) (hr : r ≤ n + 1) :
    Module.Finite R ((DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj (HodgeLayer.HodgeLayerDerivedFiniteness.tail K r))⟦(n : ℤ)⟧) := by
  induction hr using Nat.decreasingInduction with
  | self => exact HodgeLayer.HodgeLayerDerivedFiniteness.last_tail_finite R A K n
  | of_succ r hr ih =>
      have hrn : r ≤ n := by omega
      let : Module.Finite R (Abelian.Ext.{w} A (K.X r) (n - r)) := hterms r hrn
      let S := (HodgeTruncationIs.HodgeTruncationLayer.sequence K r).map (ComplexShape.embeddingUpNat.extendFunctor C)
      have hS : S.ShortExact := NumberTheory.PadicHodge.GeometricComparison.ExtendShort.ExtendShortExact.shortExact _ _ (HodgeTruncationIs.HodgeTruncationLayer.shortExact K r)
      let T := (shiftFunctor (Triangle (DerivedCategory C)) (n : ℤ)).obj
        (DerivedCategory.triangleOfSES hS)
      have hT : T ∈ distTriang (DerivedCategory C) :=
        Triangle.shift_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) n
      let : Module.Finite R ((DerivedCategory.singleFunctor C 0).obj A ⟶ T.obj₁) := ih
      let : Module.Finite R ((DerivedCategory.singleFunctor C 0).obj A ⟶ T.obj₃) :=
        HodgeLayer.HodgeLayerDerivedFiniteness.layer_finite R A K r n hrn
      exact NumberTheory.PadicHodge.GeometricComparison.TriangleFinitenessFinite.TriangleFiniteness.finite R T hT ((DerivedCategory.singleFunctor C 0).obj A)

theorem finite (n : ℕ)
    (hterms : ∀ r, r ≤ n → Module.Finite R (Abelian.Ext.{w} A (K.X r) (n - r))) :
    Module.Finite R ((DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(n : ℤ)⟧) := by
  let : Module.Finite R ((DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj (HodgeLayer.HodgeLayerDerivedFiniteness.tail K 0))⟦(n : ℤ)⟧) :=
    tail_finite R A K n hterms 0 (Nat.zero_le _)
  let : IsIso (HodgeFiltrationD.HodgeFiltration.inclusion K 0) :=
    NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE.TruncationBounds.isIso_inclusion_of_nonpositive K 0 le_rfl
  let e := (shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso
    (DerivedCategory.Q.mapIso ((ComplexShape.embeddingUpNat.extendFunctor C).mapIso
      (asIso (HodgeFiltrationD.HodgeFiltration.inclusion K 0))))
  let f : ((DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj (HodgeLayer.HodgeLayerDerivedFiniteness.tail K 0))⟦(n : ℤ)⟧) ≃ₗ[R]
        ((DerivedCategory.singleFunctor C 0).obj A ⟶
          (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(n : ℤ)⟧) :=
    Linear.homCongr R (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A)) e
  exact Module.Finite.equiv f

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ConnectiveHypercohomology.ConnectiveHypercohomologyFiniteness
