import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space
import Mathlib.RingTheory.Polynomial.Ideal

/-! # Zero Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroSection.BundleCycles

noncomputable section

/-! # LineBundleCycles: the polynomial zero section and its actual coordinate vanishing locus -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

def polynomialZeroSection : Spec (.of R) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom Polynomial.constantCoeff)

theorem polynomialZeroSection_projection : polynomialZeroSection R ≫ Projection.BundleCycles.polynomialProjection R = 𝟙 _ := by
  have h : CommRingCat.ofHom (algebraMap R (Polynomial R)) ≫
      CommRingCat.ofHom (Polynomial.constantCoeff : Polynomial R →+* R) = 𝟙 (CommRingCat.of R) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact Polynomial.coeff_C_zero
  exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h).trans (Spec.map_id _))

theorem polynomialZeroSection_coordinate :
    (polynomialZeroSection R).appTop (AffineLine.Space.BundleCycles.polynomialCoordinateSection R) = 0 := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.constantCoeff : Polynomial R →+* R))) Polynomial.X
  change (Scheme.ΓSpecIso (.of R)).inv (Polynomial.constantCoeff Polynomial.X) =
    (polynomialZeroSection R).appTop (AffineLine.Space.BundleCycles.polynomialCoordinateSection R) at h
  have hX : Polynomial.constantCoeff (Polynomial.X : Polynomial R) = 0 := Polynomial.coeff_X_zero
  simpa only [hX, map_zero] using h.symm

theorem polynomialZeroSection_affineSpace :
    polynomialZeroSection R ≫ (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv R).hom = AffineLine.Space.BundleCycles.affineLineZeroSection (Spec (.of R)) := by
  apply AffineSpace.hom_ext
  · change (_ ≫ _) ≫ _ = AffineLine.Space.BundleCycles.affineLineZeroSection (Spec (.of R)) ≫ AffineLine.Charts.BundleCycles.affineLineProjection (Spec (.of R))
    rw [Category.assoc, LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv_over, polynomialZeroSection_projection,
      AffineLine.Space.BundleCycles.affineLineZeroSection_projection]
  · intro i
    cases i
    change (polynomialZeroSection R ≫ (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv R).hom).appTop
      (AffineLine.Space.BundleCycles.affineLineCoordinate (Spec (.of R))) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineLine.Space.BundleCycles.polynomialAffineSpaceEquiv_coordinate,
      polynomialZeroSection_coordinate]
    exact (AffineLine.Space.BundleCycles.affineLineZeroSection_coordinate (Spec (.of R))).symm

theorem polynomialZeroSection_range :
    Set.range (polynomialZeroSection R) =
      ((Spec (.of (Polynomial R))).basicOpen (AffineLine.Space.BundleCycles.polynomialCoordinateSection R) : Set (Spec (.of (Polynomial R))))ᶜ := by
  have h : Function.Surjective (Polynomial.constantCoeff : Polynomial R →+* R) :=
    fun a => ⟨Polynomial.C a, Polynomial.coeff_C_zero⟩
  change Set.range (PrimeSpectrum.comap (Polynomial.constantCoeff : Polynomial R →+* R)) = _
  rw [range_comap_of_surjective _ _ h, Polynomial.ker_constantCoeff]
  change PrimeSpectrum.zeroLocus (Ideal.span {(Polynomial.X : Polynomial R)} : Set (Polynomial R)) =
    ((Spec (.of (Polynomial R))).basicOpen
      ((Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X) : Set (Spec (.of (Polynomial R))))ᶜ
  rw [basicOpen_eq_of_affine]
  ext p
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  change Ideal.span {Polynomial.X} ≤ p.asIdeal ↔ ¬Polynomial.X ∉ p.asIdeal
  exact (Ideal.span_singleton_le_iff_mem (I := p.asIdeal)).trans not_not.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroSection.BundleCycles
