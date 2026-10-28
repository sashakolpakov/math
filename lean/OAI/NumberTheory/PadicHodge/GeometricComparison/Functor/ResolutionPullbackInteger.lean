import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionInteger

/-! # Resolution Pullback Integer -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackInteger.FunctorResolutionPullbackTotal

noncomputable section

/-! The constructed pullback on total resolutions preserves the original augmentation after extension to integer degrees. -/

open _root_.CategoryTheory Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasCoproducts.{0} D]
  (F : C ⥤ D) [F.Additive]
  (T : C ⥤ CochainComplex C ℕ) [T.Additive]
  (N : D ⥤ CochainComplex D ℕ) [N.Additive]
  (a : T ⋙ F.mapHomologicalComplex (.up ℕ) ⟶ F ⋙ N)

def integerMap (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (ResolutionInteger.FunctorResolutionInteger.total T K) ⟶
      ResolutionInteger.FunctorResolutionInteger.total N ((F.mapHomologicalComplex (.up ℕ)).obj K) :=
  (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat (ResolutionTotal.FunctorResolutionTotal.total T K)).hom ≫
    HomologicalComplex.extendMap (ResolutionPullbackTotal.FunctorResolutionPullbackTotal.map F T N a K) ComplexShape.embeddingUpNat

variable (η : CochainComplex.single₀ C ⟶ T) (θ : CochainComplex.single₀ D ⟶ N)
  (ha : ∀ P, F.map ((η.app P).f 0) ≫ (a.app P).f 0 = (θ.app (F.obj P)).f 0)

include ha in
theorem integerAugmentation (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map (ResolutionInteger.FunctorResolutionInteger.edge T η K) ≫ integerMap F T N a K =
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat K).hom ≫
        ResolutionInteger.FunctorResolutionInteger.edge N θ ((F.mapHomologicalComplex (.up ℕ)).obj K) := by
  have h₁ := AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso_naturality F ComplexShape.embeddingUpNat
    (ResolutionTotal.FunctorResolutionTotal.edge T η K)
  have h₂ := (HomologicalComplex.extendMap_comp
    ((F.mapHomologicalComplex (.up ℕ)).map (ResolutionTotal.FunctorResolutionTotal.edge T η K))
    (ResolutionPullbackTotal.FunctorResolutionPullbackTotal.map F T N a K) ComplexShape.embeddingUpNat).symm.trans
      (congrArg (fun k => HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)
        (ResolutionPullbackTotal.FunctorResolutionPullbackTotal.augmentation F T N a η θ ha K))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ HomologicalComplex.extendMap (ResolutionPullbackTotal.FunctorResolutionPullbackTotal.map F T N a K) ComplexShape.embeddingUpNat) h₁).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat K).hom ≫ k) h₂)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackInteger.FunctorResolutionPullbackTotal
