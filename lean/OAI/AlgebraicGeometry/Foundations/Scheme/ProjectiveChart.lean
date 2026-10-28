import OAI.AlgebraicGeometry.Foundations.Scheme.PolynomialToProjectiveChart
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Projective Chart -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart

noncomputable section

/-!
# Standard coordinate charts of the actual projective scheme

The coordinate basic open of `Proj ℂ[X₀,...,Xₙ]` is identified with the spectrum
of the polynomial ring in the remaining `n` coordinates, and hence with
mathlib's actual affine-space scheme. The isomorphisms commute with the given
morphisms to `Spec ℂ`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The coefficient-field structure map on the polynomial affine chart. -/
abbrev projectiveChartPolynomialToBase (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) ⟶ ProjectiveSpace.complexBase :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* ProjectiveChartToPolynomial.projectiveChartPolynomial n i))

@[simp]
theorem projectiveChartRingEquiv_coe (n : ℕ) (i : Fin (n + 1)) :
    (PolynomialToProjectiveChart.projectiveChartRingEquiv n i : ProjectiveChartToPolynomial.projectiveChartRing n i →+* ProjectiveChartToPolynomial.projectiveChartPolynomial n i) =
      ProjectiveChartToPolynomial.projectiveChartToPolynomial n i := by
  ext x
  rfl

/-- The genuine coordinate basic open is the affine spectrum of its polynomial
coordinate ring, by the proved homogeneous-localization ring equivalence. -/
def projectiveCoordinateIsoSpec (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).toScheme ≅ Spec (.of (ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) :=
  Proj.basicOpenIsoSpec (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1) ≪≫
    Scheme.Spec.mapIso (PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm.toCommRingCatIso.op

/-- On the inverse chart map, the scheme morphism is induced by the explicit
ring homomorphism sending homogeneous fractions to dehomogenized polynomials. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_ι (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec n i).inv ≫ (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι =
      Spec.map (CommRingCat.ofHom (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)) ≫
        Proj.awayι (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
          (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1) := by
  simp [projectiveCoordinateIsoSpec, Proj.awayι, Category.assoc]

/-- The inverse chart identification is a morphism over the complex base. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec n i).inv ≫ (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫
      ProjectiveSpace.projectiveSpaceToBase n = projectiveChartPolynomialToBase n i := by
  rw [projectiveCoordinateIsoSpec_inv_ι_assoc, ProjectiveSpace.projectiveSpaceToBase_chart]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact ProjectiveChartToPolynomial.projectiveChartToPolynomial_constants n i c

/-- The chart isomorphism respects the actual structure morphisms to `Spec ℂ`. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec n i).hom ≫ projectiveChartPolynomialToBase n i =
      (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫ ProjectiveSpace.projectiveSpaceToBase n := by
  apply (cancel_epi (projectiveCoordinateIsoSpec n i).inv).mp
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
    (projectiveCoordinateIsoSpec_inv_over n i).symm

/-- The same chart comparison as an isomorphism in the category over `Spec ℂ`. -/
def projectiveCoordinateOverIso (n : ℕ) (i : Fin (n + 1)) :
    Over.mk ((ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫ ProjectiveSpace.projectiveSpaceToBase n) ≅
      Over.mk (projectiveChartPolynomialToBase n i) :=
  Over.isoMk (projectiveCoordinateIsoSpec n i) (projectiveCoordinateIsoSpec_over n i)

/-- The standard polynomial affine chart map into projective space. -/
def projectiveAffineChartMap (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) ⟶ ProjectiveSpace.projectiveSpace n :=
  (projectiveCoordinateIsoSpec n i).inv ≫ (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι

instance (n : ℕ) (i : Fin (n + 1)) : IsOpenImmersion (projectiveAffineChartMap n i) := by
  dsimp [projectiveAffineChartMap]
  infer_instance

@[reassoc]
theorem projectiveAffineChartMap_over (n : ℕ) (i : Fin (n + 1)) :
    projectiveAffineChartMap n i ≫ ProjectiveSpace.projectiveSpaceToBase n =
      projectiveChartPolynomialToBase n i := by
  exact projectiveCoordinateIsoSpec_inv_over n i

/-- The omitted-coordinate index has exactly `n` elements. -/
theorem projectiveChartCoordinate_card (n : ℕ) (i : Fin (n + 1)) :
    Fintype.card {j : Fin (n + 1) // j ≠ i} = n := by
  rw [Fintype.card_subtype_compl (fun j : Fin (n + 1) => j = i)]
  simp

/-- Each actual projective coordinate open is mathlib's affine `n`-space,
indexed by the `n` homogeneous coordinates other than the normalized one. -/
def projectiveCoordinateIsoAffineSpace (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).toScheme ≅
      AffineSpace {j : Fin (n + 1) // j ≠ i} ProjectiveSpace.complexBase :=
  projectiveCoordinateIsoSpec n i ≪≫
    (AffineSpace.SpecIso {j : Fin (n + 1) // j ≠ i} (.of ℂ)).symm

/-- The identification with native affine space also respects the complex base. -/
@[reassoc]
theorem projectiveCoordinateIsoAffineSpace_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoAffineSpace n i).hom ≫
      (AffineSpace {j : Fin (n + 1) // j ≠ i} ProjectiveSpace.complexBase ↘ ProjectiveSpace.complexBase) =
      (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫ ProjectiveSpace.projectiveSpaceToBase n := by
  change ((projectiveCoordinateIsoSpec n i).hom ≫
      (AffineSpace.SpecIso {j : Fin (n + 1) // j ≠ i} (.of ℂ)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over]
  exact projectiveCoordinateIsoSpec_over n i

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
