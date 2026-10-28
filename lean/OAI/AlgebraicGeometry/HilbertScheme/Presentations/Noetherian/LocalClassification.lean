import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.NoetherianInjectivity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.LocalChartLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalParameter

/-! # Local Classification -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalClassification.GradedHilbert

noncomputable section

/-! Unique actual Hilbert parameters for native polynomial families over
local noetherian test rings, including nonreduced local rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {R : Type u} [CommRing R]

theorem boundedHilbertUniversalFamily_residue_polynomial
    (q : ℕ → ℕ) (P : Polynomial ℚ) (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P)
    (f : Spec (.of R) ⟶ S) (x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q)
    (p : PrimeSpectrum R) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q))))).toIdeal P := by
  let g := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f (algebraMap R p.asIdeal.ResidueField)
  have h := BoundedHilbert.FieldFamily.GradedHilbert.boundedHilbertUniversalFamily_field_polynomial q P hP _ (g ≫ x)
  rw [Hilbert.Functor.pullbackFamily_comp, Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange] at h
  exact h

variable [IsLocalRing R] [IsNoetherianRing R]

theorem boundedHilbertUniversalFamily_local_injective (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) (f : Spec (.of R) ⟶ S) :
    Function.Injective (fun x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q =>
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q)) := by
  intro x y h
  change Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
    (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q) =
    Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) y
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q) at h
  obtain ⟨a, xa, hxa⟩ := BoundedHilbert.LocalChartLift.GradedHilbert.boundedHilbert_local_chart_lift q f x
  obtain ⟨b, yb, hyb⟩ := BoundedHilbert.LocalChartLift.GradedHilbert.boundedHilbert_local_chart_lift q f y
  rw [← hxa, ← hyb, BoundedHilbert.FieldFamily.GradedHilbert.boundedHilbertUniversalFamily_chart_family,
    BoundedHilbert.FieldFamily.GradedHilbert.boundedHilbertUniversalFamily_chart_family] at h
  apply (cancel_mono (BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S q)).mp
  rw [← hxa, ← hyb, Category.assoc, Category.assoc,
    BoundedHilbert.ChartPullback.GradedHilbert.boundedHilbertChartOverMap_parameter, BoundedHilbert.ChartPullback.GradedHilbert.boundedHilbertChartOverMap_parameter,
    ← Category.assoc, ← Category.assoc]
  exact NormalizedHilbert.NoetherianInjectivity.GradedHilbert.normalizedHilbertNativeFamily_noetherian_parameter_injective a b f q P hP hN hr _ _ _ _ h

theorem existsUnique_noetherian_local_hilbert_parameter (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  obtain ⟨x, hx⟩ := LocalParameter.GradedHilbert.exists_noetherian_local_hilbert_parameter f F P hP N hN ι hr
  let p : PrimeSpectrum R := IsLocalRing.closedPoint R
  let J := Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))
  have hreal : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P :=
    Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile_realizes J (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _) P (hP p) N
      ((le_max_right _ _).trans hN)
  exact ⟨x, hx, fun y hy => boundedHilbertUniversalFamily_local_injective _ P hreal hN hr f (hy.trans hx.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalClassification.GradedHilbert
