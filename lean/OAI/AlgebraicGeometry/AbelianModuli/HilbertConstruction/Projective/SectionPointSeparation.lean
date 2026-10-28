import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointGlobalEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.RatioFieldCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FinitePointSectionAvoidance

/-! # Section Point Separation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionPointSeparation

noncomputable section

/-! A covering family of line-bundle sections with affine charts and
generating ratios separates a rational point from any different scheme
point. Over an infinite field one section does this simultaneously for
any finite collection of points away from the rational point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem exists_section_separating_rationalPoint
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Section.ProjectivePresentation.SectionRatiosGenerate p s)
    (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (x : X) (hx : x ≠ z (IsLocalRing.closedPoint K)) :
    ∃ t : Line.Bundles.structureModule X ⟶ L.sheaf,
      z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing t ∧
      x ∈ Ample.LineBundles.sectionNonvanishing t := by
  classical
  by_contra h
  have hall (t : Line.Bundles.structureModule X ⟶ L.sheaf)
      (ht : z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing t) :
      x ∉ Ample.LineBundles.sectionNonvanishing t := fun hxt => h ⟨t, ht, hxt⟩
  obtain ⟨i, hiz⟩ := hcover (z (IsLocalRing.closedPoint K))
  let U := Ample.LineBundles.sectionNonvanishing (s i)
  let q := U.ι ≫ p
  have hrange : Set.range z ⊆ (U : Set X) := by
    rintro _ ⟨a, rfl⟩
    have he : a = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    change z a ∈ Ample.LineBundles.sectionNonvanishing (s i)
    rw [he]
    exact hiz
  let τ := IsOpenImmersion.lift U.ι z ((Scheme.Opens.range_ι U).symm ▸ hrange)
  have hτ : τ ≫ U.ι = z := IsOpenImmersion.lift_fac _ _ _
  have hτq : τ ≫ q = 𝟙 _ := by
    change τ ≫ (U.ι ≫ p) = 𝟙 _
    rw [← Category.assoc, hτ, hz]
  have hτz : U.ι (τ (IsLocalRing.closedPoint K)) = z (IsLocalRing.closedPoint K) :=
    congrArg (fun f : Spec (.of K) ⟶ X => f (IsLocalRing.closedPoint K)) hτ
  let c (j : Fin (n + 1)) := Rational.PointGlobalEvaluation.rationalPointGlobalEvaluation q τ hτq (Section.Frames.sectionRatio (s i) (s j))
  let t (j : Fin (n + 1)) := s j - Coefficient.ScalarSections.coefficientScalarSection p (c j) (s i)
  have htz (j : Fin (n + 1)) : z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing (t j) := by
    have heval : Rational.PointGlobalEvaluation.rationalPointGlobalEvaluation q τ hτq (Section.Frames.sectionRatio (s i) (t j)) = 0 := by
      rw [Section.RatioFieldCoordinates.sectionRatio_coefficientDifference, map_sub, Rational.PointGlobalEvaluation.rationalPointGlobalEvaluation_coefficient]
      exact sub_self _
    have hn := (Rational.PointGlobalEvaluation.rationalPointGlobalEvaluation_eq_zero q τ hτq _).mp heval
    rw [Section.RatioFieldCoordinates.sectionRatio_basicOpen] at hn
    change U.ι (τ (IsLocalRing.closedPoint K)) ∉ Ample.LineBundles.sectionNonvanishing (t j) at hn
    rwa [hτz] at hn
  have htx (j : Fin (n + 1)) : x ∉ Ample.LineBundles.sectionNonvanishing (t j) := hall (t j) (htz j)
  have hix : x ∈ U := by
    obtain ⟨j, hj⟩ := hcover x
    have hsum : s j = t j + Coefficient.ScalarSections.coefficientScalarSection p (c j) (s i) :=
      (sub_add_cancel _ _).symm
    rw [hsum] at hj
    rcases L.sectionNonvanishing_add_le _ _ hj with ht | hc
    · exact False.elim (htx j ht)
    · exact Coefficient.ScalarSections.coefficientScalarSection_nonvanishing_le p L (c j) (s i) hc
  let y : U.toScheme := ⟨x, hix⟩
  have : IsAffine U.toScheme := ha i
  have he : y = τ (IsLocalRing.closedPoint K) := by
    apply Rational.PointGlobalEvaluation.affineScheme_eq_rationalPoint_of_generators q τ hτq
      (fun j => Section.Frames.sectionRatio (s i) (s j)) (Section.ProjectivePresentation.SectionRatiosGenerate.overField p s hgen i) y
    intro j
    change y ∉ U.toScheme.basicOpen (Section.Frames.sectionRatio (s i) (s j) - Coefficient.ModulePresheaf.schemeCoefficientMap q (c j))
    rw [← Section.RatioFieldCoordinates.sectionRatio_coefficientDifference p (s i) (s j) (c j), Section.RatioFieldCoordinates.sectionRatio_basicOpen]
    exact htx j
  exact hx ((congrArg (fun a : U.toScheme => U.ι a) he).trans hτz)

theorem exists_section_vanishing_at_rationalPoint_avoiding_finite_points [Infinite K]
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Section.ProjectivePresentation.SectionRatiosGenerate p s)
    (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    {ι : Type v} [Finite ι] (x : ι → X)
    (hx : ∀ i, x i ≠ z (IsLocalRing.closedPoint K)) :
    ∃ t : Line.Bundles.structureModule X ⟶ L.sheaf,
      z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing t ∧
      ∀ i, x i ∈ Ample.LineBundles.sectionNonvanishing t :=
  FinitePointSectionAvoidance.exists_section_vanishing_and_nonvanishing_at_finite_points p L _ x
    (fun i => exists_section_separating_rationalPoint p L s hcover ha hgen z hz (x i) (hx i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionPointSeparation
