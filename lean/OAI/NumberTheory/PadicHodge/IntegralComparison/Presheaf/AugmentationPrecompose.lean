import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationEdge

/-! # Augmentation Precompose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationPrecompose

noncomputable section

/-! Precomposing the literal coefficient augmentation commutes with
its native Čech total edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  {A B : Cᵒᵖ ⥤ ModuleCat.{max w t} R} (f : A ⟶ B)
  (a : A ⟶ P.X 0) (ha : a ≫ P.d 0 1 = 0)
  (b : B ⟶ P.X 0) (hb : b ≫ P.d 0 1 = 0) (h : f ≫ b = a)

local instance coefficientProducts : HasProducts.{w} (ModuleCat.{max w t} R) :=
  fun T => (ModuleCat.hasLimitsOfSize.{w, w, max w t, r}).has_limits_of_shape (Discrete T)

include h in
theorem map : (FormalCoproduct.cochainComplexFunctor N).map f ≫
    AugmentationProduct.map N P B b hb =
      AugmentationProduct.map N P A a ha := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((FormalCoproduct.cochainComplexFunctor N).map f).f n ≫
      ((AugmentationProduct.rowMap.{u,v,w,t,r} N P B b).f n ≫ (TotalCup.CechProduct.bicomplex.{u,v,w,t,r} N P).ιTotal (.up ℕ) 0 n n (Nat.zero_add n)) =
    (AugmentationProduct.rowMap.{u,v,w,t,r} N P A a).f n ≫ (TotalCup.CechProduct.bicomplex.{u,v,w,t,r} N P).ιTotal (.up ℕ) 0 n n (Nat.zero_add n)
  have hn := congrArg (fun α : AugmentationProduct.source.{u,v,w,t,r} N A ⟶ AugmentationProduct.source.{u,v,w,t,r} N (P.X 0) => α.f n)
    (((FormalCoproduct.cochainComplexFunctor N).map_comp f b).symm.trans
      (congrArg (FormalCoproduct.cochainComplexFunctor N).map h))
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun α => α ≫ (TotalCup.CechProduct.bicomplex.{u,v,w,t,r} N P).ιTotal (.up ℕ) 0 n n (Nat.zero_add n)) hn)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationPrecompose
