import OAI.RepresentationTheory.Theta.Geometric.Projective.Map
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Chart Schemes -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.ChartSchemes.RelativeProjective

noncomputable section

/-! The standard relative projective charts are the actual polynomial
spectra and affine spaces, including the scalar structure morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R]

/-- The coefficient-field structure map on the polynomial affine chart. -/
abbrev projectiveChartPolynomialToBase (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (Charts.RelativeProjective.projectiveChartPolynomial R n i)) ⟶ (Spec (.of R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* Charts.RelativeProjective.projectiveChartPolynomial R n i))

@[simp]
theorem projectiveChartRingEquiv_coe (n : ℕ) (i : Fin (n + 1)) :
    (Charts.RelativeProjective.projectiveChartRingEquiv R n i : Charts.RelativeProjective.projectiveChartRing R n i →+* Charts.RelativeProjective.projectiveChartPolynomial R n i) =
      Charts.RelativeProjective.projectiveChartToPolynomial R n i := by
  ext x
  rfl

/-- The genuine coordinate basic open is the affine spectrum of its polynomial
coordinate ring, by the proved homogeneous-localization ring equivalence. -/
def projectiveCoordinateIsoSpec (n : ℕ) (i : Fin (n + 1)) :
    (Map.RelativeProjective.projectiveCoordinateOpen R n i).toScheme ≅ Spec (.of (Charts.RelativeProjective.projectiveChartPolynomial R n i)) :=
  Proj.basicOpenIsoSpec (Charts.RelativeProjective.projectiveGrading R n) (MvPolynomial.X i)
      (Charts.RelativeProjective.projectiveVariable_homogeneous R n i) (by decide : 0 < 1) ≪≫
    Scheme.Spec.mapIso (Charts.RelativeProjective.projectiveChartRingEquiv R n i).symm.toCommRingCatIso.op

/-- On the inverse chart map, the scheme morphism is induced by the explicit
ring homomorphism sending homogeneous fractions to dehomogenized polynomials. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_ι (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec R n i).inv ≫ (Map.RelativeProjective.projectiveCoordinateOpen R n i).ι =
      Spec.map (CommRingCat.ofHom (Charts.RelativeProjective.projectiveChartToPolynomial R n i)) ≫
        Proj.awayι (Charts.RelativeProjective.projectiveGrading R n) (MvPolynomial.X i)
          (Charts.RelativeProjective.projectiveVariable_homogeneous R n i) (by decide : 0 < 1) := by
  simp [projectiveCoordinateIsoSpec, Proj.awayι, Category.assoc]

/-- The inverse chart identification is a morphism over the complex base. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec R n i).inv ≫ (Map.RelativeProjective.projectiveCoordinateOpen R n i).ι ≫
      Map.RelativeProjective.projectiveSpaceToBase R n = projectiveChartPolynomialToBase R n i := by
  rw [projectiveCoordinateIsoSpec_inv_ι_assoc, Map.RelativeProjective.projectiveSpaceToBase_chart]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact Charts.RelativeProjective.projectiveChartToPolynomial_constants R n i c

/-- The chart isomorphism respects the actual structure morphisms to `Spec R`. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec R n i).hom ≫ projectiveChartPolynomialToBase R n i =
      (Map.RelativeProjective.projectiveCoordinateOpen R n i).ι ≫ Map.RelativeProjective.projectiveSpaceToBase R n := by
  apply (cancel_epi (projectiveCoordinateIsoSpec R n i).inv).mp
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
    (projectiveCoordinateIsoSpec_inv_over R n i).symm

/-- The same chart comparison as an isomorphism in the category over `Spec R`. -/
def projectiveCoordinateOverIso (n : ℕ) (i : Fin (n + 1)) :
    Over.mk ((Map.RelativeProjective.projectiveCoordinateOpen R n i).ι ≫ Map.RelativeProjective.projectiveSpaceToBase R n) ≅
      Over.mk (projectiveChartPolynomialToBase R n i) :=
  Over.isoMk (projectiveCoordinateIsoSpec R n i) (projectiveCoordinateIsoSpec_over R n i)

/-- The standard polynomial affine chart map into projective space. -/
def projectiveAffineChartMap (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (Charts.RelativeProjective.projectiveChartPolynomial R n i)) ⟶ Map.RelativeProjective.projectiveSpace R n :=
  (projectiveCoordinateIsoSpec R n i).inv ≫ (Map.RelativeProjective.projectiveCoordinateOpen R n i).ι

instance (n : ℕ) (i : Fin (n + 1)) : IsOpenImmersion (projectiveAffineChartMap R n i) := by
  dsimp [projectiveAffineChartMap]
  infer_instance

@[reassoc]
theorem projectiveAffineChartMap_over (n : ℕ) (i : Fin (n + 1)) :
    projectiveAffineChartMap R n i ≫ Map.RelativeProjective.projectiveSpaceToBase R n =
      projectiveChartPolynomialToBase R n i := by
  exact projectiveCoordinateIsoSpec_inv_over R n i

/-- The omitted-coordinate index has exactly `n` elements. -/
theorem projectiveChartCoordinate_card (n : ℕ) (i : Fin (n + 1)) :
    Fintype.card {j : Fin (n + 1) // j ≠ i} = n := by
  rw [Fintype.card_subtype_compl (fun j : Fin (n + 1) => j = i)]
  simp

/-- Each actual projective coordinate open is mathlib's affine `n`-space,
indexed by the `n` homogeneous coordinates other than the normalized one. -/
def projectiveCoordinateIsoAffineSpace (n : ℕ) (i : Fin (n + 1)) :
    (Map.RelativeProjective.projectiveCoordinateOpen R n i).toScheme ≅
      AffineSpace {j : Fin (n + 1) // j ≠ i} (Spec (.of R)) :=
  projectiveCoordinateIsoSpec R n i ≪≫
    (AffineSpace.SpecIso {j : Fin (n + 1) // j ≠ i} (.of R)).symm

/-- The identification with native affine space also respects the complex base. -/
@[reassoc]
theorem projectiveCoordinateIsoAffineSpace_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoAffineSpace R n i).hom ≫
      (AffineSpace {j : Fin (n + 1) // j ≠ i} (Spec (.of R)) ↘ (Spec (.of R))) =
      (Map.RelativeProjective.projectiveCoordinateOpen R n i).ι ≫ Map.RelativeProjective.projectiveSpaceToBase R n := by
  change ((projectiveCoordinateIsoSpec R n i).hom ≫
      (AffineSpace.SpecIso {j : Fin (n + 1) // j ≠ i} (.of R)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over]
  exact projectiveCoordinateIsoSpec_over R n i

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.ChartSchemes.RelativeProjective
