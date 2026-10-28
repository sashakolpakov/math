import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.AffineSpace
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties

/-! # Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Charts.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual polynomial charts for the relative affine line over any scheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (X : Scheme.{0})

instance affineLineBaseChart_isOpenImmersion (U : X.affineOpens) : IsOpenImmersion U.2.fromSpec :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2

abbrev affineLine : Scheme := AffineSpace PUnit X

def affineLineProjection : affineLine X ⟶ X := AffineSpace PUnit X ↘ X

def affineLinePolynomialChart (U : X.affineOpens) :
    Spec (.of (Polynomial Γ(X, U.1))) ⟶ affineLine X :=
  (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)).hom ≫ AffineSpace.map PUnit U.2.fromSpec

theorem affineLinePolynomialChart_toBase (U : X.affineOpens) :
    affineLinePolynomialChart X U ≫ affineLineProjection X = LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) ≫ U.2.fromSpec := by
  change ((LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)).hom ≫ AffineSpace.map PUnit U.2.fromSpec) ≫ (AffineSpace PUnit X ↘ X) = _
  rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv_over]

theorem affineLinePolynomialChart_isPullback (U : X.affineOpens) :
    IsPullback (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1)) (affineLinePolynomialChart X U)
      U.2.fromSpec (affineLineProjection X) := by
  let e := LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)
  apply (AffineSpace.isPullback_map (n := PUnit) U.2.fromSpec).flip.of_iso e.symm (.refl _) (.refl _) (.refl _)
  · change _ ≫ 𝟙 _ = e.inv ≫ _
    apply (cancel_epi e.hom).mp
    rw [Category.comp_id, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv_over Γ(X, U.1)
  · change _ ≫ 𝟙 _ = e.inv ≫ (e.hom ≫ _)
    rw [Category.comp_id, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

instance affineLinePolynomialChart_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (affineLinePolynomialChart X U) := by
  have h : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact MorphismProperty.of_isPullback (affineLinePolynomialChart_isPullback X U) h

theorem affineLinePolynomialChart_range (U : X.affineOpens) :
    Set.range (affineLinePolynomialChart X U) = affineLineProjection X ⁻¹' (U.1 : Set X) := by
  have h := Scheme.image_preimage_eq_of_isPullback (affineLinePolynomialChart_isPullback X U) Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  exact h.trans (congrArg (fun A : Set X => affineLineProjection X ⁻¹' A) U.2.range_fromSpec)

theorem affineLinePolynomialChart_covers (x : affineLine X) :
    ∃ (U : X.affineOpens) (y : Spec (.of (Polynomial Γ(X, U.1)))),
      affineLinePolynomialChart X U y = x := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (affineLineProjection X x))
  have h : x ∈ Set.range (affineLinePolynomialChart X ⟨U, hU⟩) :=
    (congrArg (fun A : Set (affineLine X) => x ∈ A) (affineLinePolynomialChart_range X ⟨U, hU⟩)).mpr hx
  obtain ⟨y, hy⟩ := h
  exact ⟨⟨U, hU⟩, y, hy⟩

def affineLinePolynomialCover : (affineLine X).OpenCover :=
  Scheme.Cover.mkOfCovers X.affineOpens (fun U => Spec (.of (Polynomial Γ(X, U.1))))
    (affineLinePolynomialChart X) (affineLinePolynomialChart_covers X)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Charts.BundleCycles
