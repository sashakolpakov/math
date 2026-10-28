import OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardResolution
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Bicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor

/-! # Image Bicomplex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.ImageBicomplex

noncomputable section

/-! The canonical relative Godement maps act in both degrees of the actual bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

local instance godementDirectImageBicomplexAdditive : (TopologicalSheafPullback.sheafDirectImage f).Additive :=
  TopologicalSheafPullback.sheafDirectImageAdditive f

def godementDirectImageBicomplex (L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ) :
    HomologicalComplex₂ (ConstantSheafSections.ComplexSheaves X) (.up ℕ) (.up ℕ) :=
  @TotalComplexFunctor.mapBicomplex _ _ _ _ _ _ (TopologicalSheafPullback.sheafDirectImage f)
    (TopologicalSheafPullback.sheafDirectImageAdditive f) (Bicomplex.godementBicomplex Y L)

variable {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ}
  {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)

def godementDirectImageBicomplexMap :
    Bicomplex.godementBicomplex X K ⟶ godementDirectImageBicomplex f L where
  f q := PushforwardResolution.godementRelativeResolutionMap f (A := K.X q) (B := L.X q) (α.f q)
  comm' q q' _ := by
    have hα : K.d q q' ≫ α.f q' = α.f q ≫ (TopologicalSheafPullback.sheafDirectImage f).map (L.d q q') :=
      (α.comm q q').symm
    change PushforwardResolution.godementRelativeResolutionMap f (α.f q) ≫
        ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).map
          (FunctorialResolution.resolutionMap (Functor.stalkFamilyFunctor Y) (Functor.stalkFamilyUnit Y) (L.d q q')) =
      FunctorialResolution.resolutionMap (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) (K.d q q') ≫
        PushforwardResolution.godementRelativeResolutionMap f (α.f q')
    exact (PushforwardResolution.godementRelativeResolutionMap_naturality f (α.f q) (α.f q') (K.d q q') (L.d q q') hα).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.ImageBicomplex
