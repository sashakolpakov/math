import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroSection

/-! # Zero Locus -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroLocus.BundleCycles

noncomputable section

/-! # LineBundleCycles: the zero section is exactly the vanishing locus of the global affine-line coordinate -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

theorem affineLineZeroSection_chart_isPullback (U : X.affineOpens) :
    IsPullback U.2.fromSpec (LineBundles.Polynomial.ZeroSection.BundleCycles.polynomialZeroSection Γ(X, U.1)) (Space.BundleCycles.affineLineZeroSection X)
      (Charts.BundleCycles.affineLinePolynomialChart X U) := by
  let e := LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)
  apply (ZeroNaturality.BundleCycles.affineLineZeroSection_isPullback U.2.fromSpec).of_iso
    (.refl _) (.refl _) e.symm (.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change Space.BundleCycles.affineLineZeroSection (Spec Γ(X, U.1)) ≫ e.inv = 𝟙 _ ≫ _
    rw [← LineBundles.Polynomial.ZeroSection.BundleCycles.polynomialZeroSection_affineSpace, Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change _ ≫ 𝟙 _ = e.inv ≫ (e.hom ≫ _)
    rw [Category.comp_id, ← Category.assoc, e.inv_hom_id, Category.id_comp]

theorem affineLineZeroSection_range : Set.range (Space.BundleCycles.affineLineZeroSection X) =
    ((Charts.BundleCycles.affineLine X).basicOpen (Space.BundleCycles.affineLineCoordinate X) : Set (Charts.BundleCycles.affineLine X))ᶜ := by
  ext y
  obtain ⟨U, P, rfl⟩ := Charts.BundleCycles.affineLinePolynomialChart_covers X y
  have h₀ := Scheme.image_preimage_eq_of_isPullback (affineLineZeroSection_chart_isPullback X U) Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h₀
  have hb := Scheme.preimage_basicOpen_top (Charts.BundleCycles.affineLinePolynomialChart X U) (Space.BundleCycles.affineLineCoordinate X)
  rw [Space.BundleCycles.affineLineCoordinate_on_chart] at hb
  have hb' : Charts.BundleCycles.affineLinePolynomialChart X U ⁻¹'
      ((Charts.BundleCycles.affineLine X).basicOpen (Space.BundleCycles.affineLineCoordinate X) : Set (Charts.BundleCycles.affineLine X)) =
      ((Spec (.of (Polynomial Γ(X, U.1)))).basicOpen (Space.BundleCycles.polynomialCoordinateSection Γ(X, U.1)) :
        Set (Spec (.of (Polynomial Γ(X, U.1))))) :=
    congrArg (fun A : (Spec (.of (Polynomial Γ(X, U.1)))).Opens =>
      (A : Set (Spec (.of (Polynomial Γ(X, U.1)))))) hb
  change P ∈ Charts.BundleCycles.affineLinePolynomialChart X U ⁻¹' Set.range (Space.BundleCycles.affineLineZeroSection X) ↔
    P ∉ Charts.BundleCycles.affineLinePolynomialChart X U ⁻¹' ((Charts.BundleCycles.affineLine X).basicOpen (Space.BundleCycles.affineLineCoordinate X) : Set (Charts.BundleCycles.affineLine X))
  rw [← h₀, LineBundles.Polynomial.ZeroSection.BundleCycles.polynomialZeroSection_range, hb']
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroLocus.BundleCycles
