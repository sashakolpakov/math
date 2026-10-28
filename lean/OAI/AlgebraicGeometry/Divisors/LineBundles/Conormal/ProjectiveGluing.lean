import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveDiagram
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectivePullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram

/-! # Projective Gluing -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveGluing.BundleCycles

noncomputable section

/-! The actual projective augmented conormal spectra glue over the
ambient scheme using their principal-localization pullbacks. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def conormalProjectiveToCoefficients :
    ProjectiveDiagram.BundleCycles.conormalProjectiveDiagram I ⟶ (Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram I).rightOp ⋙ Scheme.Spec where
  app U := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase (Γ(X, U.1) ⧸ I.ideal U)
    ((Γ(X, U.1) ⧸ I.ideal U) × (I.ideal U).Cotangent)
  naturality {_U _V} i :=
    SymmetricProjective.Base.BundleCycles.symmetricScalarProjectiveMap_over _ _ (Augmented.SemilinearMap.BundleCycles.augmentedSemilinearMap_span _ _ (RestrictionSpan.BundleCycles.conormalRestriction_span I i))

theorem conormalProjectiveToCoefficients_equifibered : (conormalProjectiveToCoefficients I).Equifibered := by
  intro U V i
  obtain ⟨r, hr⟩ := i.le
  have hU : V.basicOpen r = U := Subtype.ext hr
  subst U
  let S := Γ(X, (V.basicOpen r).1)
  let φ : Γ(X, V.1) →+* S := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, V.1) S := φ.toAlgebra
  let : IsLocalization.Away r S := V.2.isLocalization_basicOpen r
  exact (ProjectivePullback.BundleCycles.conormalProjective_principal_isPullback (I.ideal V) S r
    (I.ideal (V.basicOpen r)) (I.map_ideal_basicOpen V r)
    (I.ideal_le_comap_ideal (X.basicOpen_le r)) (ProjectiveDiagram.BundleCycles.conormalProjectiveGradedMap_irrelevant I i)).flip

def conormalProjectiveGlueData : (directedCover X).RelativeGluingData where
  functor := ProjectiveDiagram.BundleCycles.conormalProjectiveDiagram I
  natTrans := conormalProjectiveToCoefficients I ≫
    Functor.whiskerRight (Support.CoefficientDiagram.BundleCycles.supportCoefficientMap I).rightOp Scheme.Spec ≫ (restrictIsoSpec X).inv
  equifibered := by
    have h : NatTrans.Equifibered (restrictIsoSpec X).inv :=
      NatTrans.Equifibered.of_isIso (restrictIsoSpec X).inv
    exact (conormalProjectiveToCoefficients_equifibered I).comp
      (((Support.CoefficientDiagram.BundleCycles.supportCoefficientMap_coequifibered I).rightOp.whiskerRight _).comp h)

instance conormalProjectiveGlueData_isLocallyDirected :
    ((conormalProjectiveGlueData I).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def globalConormalProjective : Scheme := (conormalProjectiveGlueData I).glued

def globalConormalProjectiveToBase : globalConormalProjective I ⟶ X :=
  (conormalProjectiveGlueData I).toBase

def globalConormalProjectiveCover : (globalConormalProjective I).OpenCover :=
  (conormalProjectiveGlueData I).cover

theorem globalConormalProjective_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((conormalProjectiveGlueData I).natTrans.app U)
      ((globalConormalProjectiveCover I).f U) U.1.ι (globalConormalProjectiveToBase I) :=
  (conormalProjectiveGlueData I).isPullback_natTrans_ι_toBase U

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveGluing.BundleCycles
