import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.PolynomialChart
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Chart X -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ChartX

noncomputable section

section

/-!
# Standard coordinate charts of the actual projective scheme

The coordinate basic open of `Proj R[X₀,...,Xₙ]` is identified with the spectrum
of the polynomial ring in the remaining `n` coordinates, and hence with
mathlib's actual affine-space scheme. The isomorphisms commute with the given
morphisms to `Spec R`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Projective

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear (grading space)

theorem base_chart (R : Type) [CommRing R] (n d : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ ProjectiveLinear.grading R n d) (hd : 0 < d) :
    Proj.awayι (ProjectiveLinear.grading R n) f hf hd ≫ ProjectiveI.Base.base R n =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (ProjectiveLinear.grading R n) (Submonoid.powers f)).comp
          (ProjectiveI.Base.constants R n).toRingHom)) := by
  rw [ProjectiveI.Base.base, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The coefficient-field structure map on the polynomial affine chart. -/
abbrev projectiveChartPolynomialToBase (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (ProjectiveChart.projectiveChartPolynomial R n i)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* ProjectiveChart.projectiveChartPolynomial R n i))

@[simp]
theorem projectiveChartRingEquiv_coe (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (PolynomialChart.Projective.projectiveChartRingEquiv R n i : ProjectiveChart.projectiveChartRing R n i →+* ProjectiveChart.projectiveChartPolynomial R n i) =
      ProjectiveChart.projectiveChartToPolynomial R n i := by
  ext x
  rfl

/-- The genuine coordinate basic open is the affine spectrum of its polynomial
coordinate ring, by the proved homogeneous-localization ring equivalence. -/
def projectiveCoordinateIsoSpec (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveI.Chart.projectiveCoordinateOpen R n i).toScheme ≅ Spec (.of (ProjectiveChart.projectiveChartPolynomial R n i)) :=
  Proj.basicOpenIsoSpec (ProjectiveLinear.grading R n) (MvPolynomial.X i)
      (ProjectiveChart.projectiveVariable_homogeneous R n i) (by decide : 0 < 1) ≪≫
    Scheme.Spec.mapIso (PolynomialChart.Projective.projectiveChartRingEquiv R n i).symm.toCommRingCatIso.op

/-- On the inverse chart map, the scheme morphism is induced by the explicit
ring homomorphism sending homogeneous fractions to dehomogenized polynomials. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_ι (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec R n i).inv ≫ (ProjectiveI.Chart.projectiveCoordinateOpen R n i).ι =
      Spec.map (CommRingCat.ofHom (ProjectiveChart.projectiveChartToPolynomial R n i)) ≫
        Proj.awayι (ProjectiveLinear.grading R n) (MvPolynomial.X i)
          (ProjectiveChart.projectiveVariable_homogeneous R n i) (by decide : 0 < 1) := by
  simp [projectiveCoordinateIsoSpec, Proj.awayι, Category.assoc]

/-- The inverse chart identification is a morphism over the complex base. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_over (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec R n i).inv ≫ (ProjectiveI.Chart.projectiveCoordinateOpen R n i).ι ≫
      ProjectiveI.Base.base R n = projectiveChartPolynomialToBase R n i := by
  rw [projectiveCoordinateIsoSpec_inv_ι_assoc, base_chart R]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact ProjectiveChart.projectiveChartToPolynomial_constants R n i c

/-- The chart isomorphism respects the actual structure morphisms to `Spec R`. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_over (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec R n i).hom ≫ projectiveChartPolynomialToBase R n i =
      (ProjectiveI.Chart.projectiveCoordinateOpen R n i).ι ≫ ProjectiveI.Base.base R n := by
  apply (cancel_epi (projectiveCoordinateIsoSpec R n i).inv).mp
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
    (projectiveCoordinateIsoSpec_inv_over R n i).symm

/-- The same chart comparison as an isomorphism in the category over `Spec R`. -/
def projectiveCoordinateOverIso (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    Over.mk ((ProjectiveI.Chart.projectiveCoordinateOpen R n i).ι ≫ ProjectiveI.Base.base R n) ≅
      Over.mk (projectiveChartPolynomialToBase R n i) :=
  Over.isoMk (projectiveCoordinateIsoSpec R n i) (projectiveCoordinateIsoSpec_over R n i)

/-- The standard polynomial affine chart map into projective space. -/
def projectiveAffineChartMap (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (ProjectiveChart.projectiveChartPolynomial R n i)) ⟶ ProjectiveLinear.space R n :=
  (projectiveCoordinateIsoSpec R n i).inv ≫ (ProjectiveI.Chart.projectiveCoordinateOpen R n i).ι

instance (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) : IsOpenImmersion (projectiveAffineChartMap R n i) := by
  dsimp [projectiveAffineChartMap]
  infer_instance

@[reassoc]
theorem projectiveAffineChartMap_over (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    projectiveAffineChartMap R n i ≫ ProjectiveI.Base.base R n =
      projectiveChartPolynomialToBase R n i := by
  exact projectiveCoordinateIsoSpec_inv_over R n i

end Projective

end

section

/-! The relative projective polynomial charts commute with changes
of coefficient ring, on their actual homogeneous localization maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace Scalars

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear (grading)
open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars (graded)
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (i : Fin (n + 1))

theorem dehomogenize_map (p : MvPolynomial (Fin (n + 1)) R) :
    Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.map f p) = MvPolynomial.map f (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i p) := by
  have h : (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (R := S) i).comp (MvPolynomial.map f) =
      (MvPolynomial.map f).comp (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (R := R) i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      by_cases hj : j = i
      · subst j
        simp
      · simp [hj]
  exact DFunLike.congr_fun h p

theorem powers : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ≤
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) S)).comap (ProjectiveI.Scalars.graded f n) := by
  rintro _ ⟨k, rfl⟩
  refine ⟨k, ?_⟩
  change MvPolynomial.X i ^ k = MvPolynomial.map f (MvPolynomial.X i ^ k)
  rw [map_pow, MvPolynomial.map_X]

def localMap : ProjectiveChart.projectiveChartRing R n i →+* ProjectiveChart.projectiveChartRing S n i :=
  HomogeneousLocalization.map (ProjectiveI.Scalars.graded f n) (Scalars.powers f n i)

theorem localMap_mk (k : ℕ) (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ ProjectiveLinear.grading R n (k • (1 : ℕ))) :
    localMap f n i (Away.mk (ProjectiveLinear.grading R n) (ProjectiveChart.projectiveVariable_homogeneous R n i) k p hp) =
      Away.mk (ProjectiveLinear.grading S n) (ProjectiveChart.projectiveVariable_homogeneous S n i) k (MvPolynomial.map f p) (hp.map f) := by
  apply HomogeneousLocalization.val_injective
  simp only [localMap, Away.mk, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  congr 1
  apply Subtype.ext
  change MvPolynomial.map f (MvPolynomial.X i ^ k) = MvPolynomial.X i ^ k
  rw [map_pow, MvPolynomial.map_X]

theorem toPolynomial (x : ProjectiveChart.projectiveChartRing R n i) :
    ProjectiveChart.projectiveChartToPolynomial S n i (localMap f n i x) =
      MvPolynomial.map f (ProjectiveChart.projectiveChartToPolynomial R n i x) := by
  obtain ⟨k, p, hp, rfl⟩ := Away.mk_surjective (ProjectiveLinear.grading R n) (ProjectiveChart.projectiveVariable_homogeneous R n i) x
  rw [localMap_mk, ProjectiveChart.projectiveChartToPolynomial_mk, ProjectiveChart.projectiveChartToPolynomial_mk]
  exact dehomogenize_map f n i p

end Scalars

end

/-! The actual scheme maps in each relative projective coordinate
chart are coefficient maps between polynomial rings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace ScalarMap

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear (grading)
open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars (graded)
open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ChartX.Scalars

theorem away_of_eq {R S : Type} [CommRing R] [CommRing S] {m n : ℕ}
    (φ : ProjectiveLinear.grading R m →+*ᵍ ProjectiveLinear.grading S n)
    (hφ : HomogeneousIdeal.irrelevant (ProjectiveLinear.grading S n) ≤ (HomogeneousIdeal.irrelevant (ProjectiveLinear.grading R m)).map φ)
    (s : MvPolynomial (Fin (m + 1)) R) (hs : s ∈ ProjectiveLinear.grading R m 1)
    (t : MvPolynomial (Fin (n + 1)) S) (ht : t ∈ ProjectiveLinear.grading S n 1) (hst : φ s = t)
    (hQ : Submonoid.powers s ≤ (Submonoid.powers t).comap φ) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map φ hQ)) ≫
        Proj.awayι (ProjectiveLinear.grading R m) s hs Nat.zero_lt_one =
      Proj.awayι (ProjectiveLinear.grading S n) t ht Nat.zero_lt_one ≫ Proj.map φ hφ := by
  subst t
  exact (Proj.awayι_comp_map φ hφ Nat.zero_lt_one s hs).symm

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (i : Fin (n + 1))

theorem graded_X : ProjectiveI.Scalars.graded f n (MvPolynomial.X i) = MvPolynomial.X i := MvPolynomial.map_X f i

theorem away :
    Spec.map (CommRingCat.ofHom (Scalars.localMap f n i)) ≫
        Proj.awayι (ProjectiveLinear.grading R n) (MvPolynomial.X i) (ProjectiveChart.projectiveVariable_homogeneous R n i) Nat.zero_lt_one =
      Proj.awayι (ProjectiveLinear.grading S n) (MvPolynomial.X i) (ProjectiveChart.projectiveVariable_homogeneous S n i) Nat.zero_lt_one ≫
        ProjectiveI.Scalars.map f n := by
  exact away_of_eq (ProjectiveI.Scalars.graded f n) (ProjectiveI.Scalars.irrelevant_le f n)
    (MvPolynomial.X i) (ProjectiveChart.projectiveVariable_homogeneous R n i)
    (MvPolynomial.X i) (ProjectiveChart.projectiveVariable_homogeneous S n i) (graded_X f n i) (Scalars.powers f n i)

theorem chart :
    Projective.projectiveAffineChartMap S n i ≫ ProjectiveI.Scalars.map f n =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map f)) ≫ Projective.projectiveAffineChartMap R n i := by
  have he : (ProjectiveChart.projectiveChartToPolynomial S n i).comp (Scalars.localMap f n i) =
      (MvPolynomial.map f).comp (ProjectiveChart.projectiveChartToPolynomial R n i) := by
    apply RingHom.ext
    exact Scalars.toPolynomial f n i
  change ((Projective.projectiveCoordinateIsoSpec S n i).inv ≫ (ProjectiveI.Chart.projectiveCoordinateOpen S n i).ι) ≫ _ =
    _ ≫ ((Projective.projectiveCoordinateIsoSpec R n i).inv ≫ (ProjectiveI.Chart.projectiveCoordinateOpen R n i).ι)
  rw [Projective.projectiveCoordinateIsoSpec_inv_ι, Projective.projectiveCoordinateIsoSpec_inv_ι,
    Category.assoc, ← away f n i, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun g : ProjectiveChart.projectiveChartRing R n i →+* ProjectiveChart.projectiveChartPolynomial S n i =>
    Spec.map (CommRingCat.ofHom g) ≫ Proj.awayι (ProjectiveLinear.grading R n) (MvPolynomial.X i)
      (ProjectiveChart.projectiveVariable_homogeneous R n i) Nat.zero_lt_one) he

end ScalarMap

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ChartX
