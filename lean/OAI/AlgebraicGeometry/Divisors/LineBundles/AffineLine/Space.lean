import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Charts
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Space -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: smoothness and Noetherianity of the actual relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

instance affineLineChartRing_noetherian [IsLocallyNoetherian X] (U : X.affineOpens) :
    IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U

instance affineLineProjection_smooth : Smooth (Charts.BundleCycles.affineLineProjection X) := by
  have : IsZariskiLocalAtSource (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Charts.BundleCycles.affineLinePolynomialCover X)
  intro U
  have h : Smooth (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) ≫ U.2.fromSpec) := by
    have h₁ := LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialProjection_smooth Γ(X, U.1)
    have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h₂ : Smooth U.2.fromSpec := inferInstance
    exact @smooth_comp _ _ (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1)) _ U.2.fromSpec h₁ h₂
  exact (congrArg (fun k => Smooth k) (Charts.BundleCycles.affineLinePolynomialChart_toBase X U)).mpr h

instance affineLineProjection_geometricallyIntegral : GeometricallyIntegral (Charts.BundleCycles.affineLineProjection X) :=
  inferInstanceAs (GeometricallyIntegral (AffineSpace PUnit X ↘ X))

instance affineLineProjection_isAffineHom : IsAffineHom (Charts.BundleCycles.affineLineProjection X) :=
  inferInstanceAs (IsAffineHom (AffineSpace PUnit X ↘ X))

instance affineLine_isLocallyNoetherian [IsLocallyNoetherian X] : IsLocallyNoetherian (Charts.BundleCycles.affineLine X) :=
  LocallyOfFiniteType.isLocallyNoetherian (Charts.BundleCycles.affineLineProjection X)

instance affineLine_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (Charts.BundleCycles.affineLine X) := by
  have : CompactSpace (Charts.BundleCycles.affineLine X) := QuasiCompact.compactSpace_of_compactSpace (Charts.BundleCycles.affineLineProjection X)
  exact ⟨⟩

end

section

/-! # LineBundleCycles: the actual closed zero section of the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

def affineLineZeroSection : X ⟶ Charts.BundleCycles.affineLine X := AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit => 0)

def affineLineCoordinate : Γ(Charts.BundleCycles.affineLine X, ⊤) := AffineSpace.coord X PUnit.unit

theorem affineLineZeroSection_projection : affineLineZeroSection X ≫ Charts.BundleCycles.affineLineProjection X = 𝟙 X :=
  AffineSpace.homOfVector_over _ _

theorem affineLineZeroSection_coordinate : (affineLineZeroSection X).appTop (affineLineCoordinate X) = 0 :=
  AffineSpace.homOfVector_appTop_coord _ _ _

instance affineLineZeroSection_isClosedImmersion : IsClosedImmersion (affineLineZeroSection X) := by
  have : IsClosedImmersion (affineLineZeroSection X ≫ Charts.BundleCycles.affineLineProjection X) :=
    (affineLineZeroSection_projection X).symm ▸ (inferInstance : IsClosedImmersion (𝟙 X))
  exact IsClosedImmersion.of_comp (affineLineZeroSection X) (Charts.BundleCycles.affineLineProjection X)

end

/-! # LineBundleCycles: the global affine-line coordinate is the actual polynomial variable on every chart -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

def polynomialCoordinateSection : Γ(Spec (.of (Polynomial R)), ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X

theorem polynomialAffineSpaceEquiv_coordinate :
    (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv R).hom.appTop (affineLineCoordinate (Spec (.of R))) =
      polynomialCoordinateSection R := by
  let a : CommRingCat.of (MvPolynomial PUnit R) ⟶ CommRingCat.of (Polynomial R) :=
    (MvPolynomial.uniqueAlgEquiv R PUnit).toRingEquiv.toCommRingCatIso.hom
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality a) (MvPolynomial.X PUnit.unit)
  have hX : a (MvPolynomial.X PUnit.unit) = Polynomial.X := MvPolynomial.eval₂_X _ _ _
  change (Scheme.ΓSpecIso (.of (Polynomial R))).inv (a (MvPolynomial.X PUnit.unit)) =
    (Spec.map a).appTop ((Scheme.ΓSpecIso (.of (MvPolynomial PUnit R))).inv (MvPolynomial.X PUnit.unit)) at hn
  rw [hX] at hn
  change (Spec.map a ≫ (AffineSpace.SpecIso PUnit (.of R)).inv).appTop
    (AffineSpace.coord (Spec (.of R)) PUnit.unit) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord]
  exact hn.symm

variable (X : Scheme.{0})

theorem affineLineCoordinate_on_chart (U : X.affineOpens) :
    (Charts.BundleCycles.affineLinePolynomialChart X U).appTop (affineLineCoordinate X) =
      polynomialCoordinateSection Γ(X, U.1) := by
  change ((LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)).hom ≫ AffineSpace.map PUnit U.2.fromSpec).appTop
    (AffineSpace.coord X PUnit.unit) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord]
  exact polynomialAffineSpaceEquiv_coordinate Γ(X, U.1)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space.BundleCycles
