import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackInteger
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFinite

/-! # Resolution Pullback Normalization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackNormalization.FunctorResolutionPullbackTotal

noncomputable section

/-! The constructed resolution pullback is the canonical finite-total comparison followed by the actual bicomplex map. -/

open _root_.CategoryTheory Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasCoproducts.{0} D]
  (F : C ⥤ D) [F.Additive]
  (T : C ⥤ CochainComplex C ℕ) [T.Additive]
  (N : D ⥤ CochainComplex D ℕ) [N.Additive]
  (a : T ⋙ F.mapHomologicalComplex (.up ℕ) ⟶ F ⋙ N)

theorem integerMap_eq (K : CochainComplex C ℕ) :
    ResolutionPullbackInteger.FunctorResolutionPullbackTotal.integerMap F T N a K =
      (Finite.TotalIso.FiniteTotalExtension.iso F (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K)).inv ≫
        (TotalFinite.IntegerTotalFunctor.functor D).map (ResolutionPullbackTotal.FunctorResolutionPullbackTotal.bicomplexMap F T N a K) := by
  let e := AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K)
  let c := AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat (ResolutionTotal.FunctorResolutionTotal.total T K)
  let m := HomologicalComplex₂.total.map (ResolutionPullbackTotal.FunctorResolutionPullbackTotal.bicomplexMap F T N a K) (.up ℕ)
  exact (congrArg (fun k => c.hom ≫ k) (HomologicalComplex.extendMap_comp e.inv m
    ComplexShape.embeddingUpNat)).trans (Category.assoc _ _ _).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackNormalization.FunctorResolutionPullbackTotal
