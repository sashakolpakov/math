import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityDiagram
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram

/-! # Infinity Gluing -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityGluing.BundleCycles

noncomputable section

/-! The actual projective conormal spectra glue over the
ambient scheme using their principal-localization pullbacks. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def conormalInfinityToCoefficients :
    InfinityDiagram.BundleCycles.conormalInfinityDiagram I ⟶ (Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram I).rightOp ⋙ Scheme.Spec where
  app U := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase (Γ(X, U.1) ⧸ I.ideal U)
    (I.ideal U).Cotangent
  naturality {_U _V} i :=
    SymmetricProjective.Base.BundleCycles.symmetricScalarProjectiveMap_over _ _ (RestrictionSpan.BundleCycles.conormalRestriction_span I i)

theorem conormalInfinityToCoefficients_equifibered : (conormalInfinityToCoefficients I).Equifibered := by
  intro U V i
  obtain ⟨r, hr⟩ := i.le
  have hU : V.basicOpen r = U := Subtype.ext hr
  subst U
  let S := Γ(X, (V.basicOpen r).1)
  let φ : Γ(X, V.1) →+* S := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, V.1) S := φ.toAlgebra
  let : IsLocalization.Away r S := V.2.isLocalization_basicOpen r
  exact (InfinityPullback.BundleCycles.conormalInfinity_principal_isPullback (I.ideal V) S r
    (I.ideal (V.basicOpen r)) (I.map_ideal_basicOpen V r)
    (I.ideal_le_comap_ideal (X.basicOpen_le r)) (InfinityDiagram.BundleCycles.conormalInfinityGradedMap_irrelevant I i)).flip

def conormalInfinityGlueData : (directedCover X).RelativeGluingData where
  functor := InfinityDiagram.BundleCycles.conormalInfinityDiagram I
  natTrans := conormalInfinityToCoefficients I ≫
    Functor.whiskerRight (Support.CoefficientDiagram.BundleCycles.supportCoefficientMap I).rightOp Scheme.Spec ≫ (restrictIsoSpec X).inv
  equifibered := by
    have h : NatTrans.Equifibered (restrictIsoSpec X).inv :=
      NatTrans.Equifibered.of_isIso (restrictIsoSpec X).inv
    exact (conormalInfinityToCoefficients_equifibered I).comp
      (((Support.CoefficientDiagram.BundleCycles.supportCoefficientMap_coequifibered I).rightOp.whiskerRight _).comp h)

instance conormalInfinityGlueData_isLocallyDirected :
    ((conormalInfinityGlueData I).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def globalConormalInfinity : Scheme := (conormalInfinityGlueData I).glued

def globalConormalInfinityToBase : globalConormalInfinity I ⟶ X :=
  (conormalInfinityGlueData I).toBase

def globalConormalInfinityCover : (globalConormalInfinity I).OpenCover :=
  (conormalInfinityGlueData I).cover

theorem globalConormalInfinity_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((conormalInfinityGlueData I).natTrans.app U)
      ((globalConormalInfinityCover I).f U) U.1.ι (globalConormalInfinityToBase I) :=
  (conormalInfinityGlueData I).isPullback_natTrans_ι_toBase U

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityGluing.BundleCycles
