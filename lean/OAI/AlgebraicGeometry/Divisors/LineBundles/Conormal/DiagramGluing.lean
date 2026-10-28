import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SymmetricDiagram
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SymmetricLocalization

/-! # Diagram Gluing -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.DiagramGluing.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual conormal symmetric diagram is compatible with affine localization -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem conormalSymmetricDiagramMap_coequifibered : (SymmetricDiagram.BundleCycles.conormalSymmetricDiagramMap I).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let φ : Γ(X, U.1) →+* Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := φ.toAlgebra
  have : IsLocalization.Away r Γ(X, V.1) := U.2.isLocalization_basicOpen r
  have hI : (I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, V.1)) = I.ideal V :=
    I.map_ideal_basicOpen U r
  have h := SymmetricLocalization.BundleCycles.conormalSymmetricRestriction_isLocalization (I.ideal U) Γ(X, V.1) (Submonoid.powers r)
    (I.ideal V) hI (I.ideal_le_comap_ideal (X.basicOpen_le r))
  let : Algebra (SymmetricAlgebra (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
      (SymmetricAlgebra (Γ(X, V.1) ⧸ I.ideal V) (I.ideal V).Cotangent) :=
    (ConormalRestriction.BundleCycles.conormalSymmetricRestriction (I.ideal U) (I.ideal V) φ
      (I.ideal_le_comap_ideal (X.basicOpen_le r))).toAlgebra
  change IsLocalization.Away
    (algebraMap (Γ(X, U.1) ⧸ I.ideal U) (SymmetricAlgebra (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
      (Ideal.Quotient.mk (I.ideal U) r))
    (SymmetricAlgebra (Γ(X, V.1) ⧸ I.ideal V) (I.ideal V).Cotangent)
  simpa only [SymmetricLocalization.BundleCycles.conormalSymmetricDenominators, Submonoid.map_powers] using h

def conormalSymmetricGlueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (conormalSymmetricDiagramMap_coequifibered I)

instance conormalSymmetricGlueData_isLocallyDirected :
    ((conormalSymmetricGlueData I).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def globalConormalSpectrum : Scheme := (conormalSymmetricGlueData I).glued

def globalConormalSpectrumProjection : globalConormalSpectrum I ⟶ X :=
  (conormalSymmetricGlueData I).toBase

def globalConormalSpectrumCover : (globalConormalSpectrum I).OpenCover :=
  (conormalSymmetricGlueData I).cover

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.DiagramGluing.BundleCycles
