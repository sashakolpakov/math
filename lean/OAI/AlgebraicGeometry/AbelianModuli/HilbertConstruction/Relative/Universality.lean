import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ClassifyingMap

/-! # Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Relative projective Hilbert families over locally noetherian tests have a unique actual parameter map, detected by equality of the embedded families on all noetherian affine tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} [IsLocallyNoetherian T.left]
variable {n B N : ℕ} {P : Polynomial ℚ} (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P)
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.classifyingMap_pullback {R : CommRingCat.{u}} [IsNoetherianRing R] (x : Spec R ⟶ T.left) :
    Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ (F.classifyingMap hN hflat htest hr).left) hflat =
      (F.affineFamily x).val := by
  rw [F.classifyingMap_affine hN hflat htest hr]
  exact Flat.ClosedUniversality.flatClosedHilbertClassifier_pullback_eq hN hflat htest hr (x ≫ T.hom) (F.affineFamily x)

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.classifyingMap_unique
    (g : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N)
    (hg : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (x : Spec R ⟶ T.left),
      Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ g.left) hflat = (F.affineFamily x).val) :
    g = F.classifyingMap hN hflat htest hr := by
  apply Over.OverMorphism.ext
  apply T.left.affineOpenCover.openCover.hom_ext
  intro i
  let R := T.left.affineOpenCover.X i
  let : IsNoetherianRing R := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian T.left i
  let x := T.left.affineOpenCover.f i
  let a : Over.mk (x ≫ T.hom) ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N :=
    Over.homMk (x ≫ g.left) (by
      rw [Category.assoc, g.w]
      rfl)
  let a₀ := Flat.ClosedParameterEquivalence.flatClosedHilbertAffinePointEquiv hN hflat htest hr (x ≫ T.hom) (F.affineFamily x)
  have he : a = a₀ := (Flat.ClosedUniversality.flatClosedHilbertParameter_universal hN hflat htest hr
    (x ≫ T.hom) (F.affineFamily x)).unique (hg R x)
      (Flat.ClosedUniversality.flatClosedHilbertClassifier_pullback_eq hN hflat htest hr (x ≫ T.hom) (F.affineFamily x))
  exact (congrArg Over.Hom.left he).trans (F.classifyingMap_affine hN hflat htest hr x).symm

include hN htest hr in
theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.existsUnique_classifyingMap :
    ∃! g : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N,
      ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (x : Spec R ⟶ T.left),
        Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ g.left) hflat = (F.affineFamily x).val :=
  ⟨F.classifyingMap hN hflat htest hr, fun _ _ x => F.classifyingMap_pullback hN hflat htest hr x,
    F.classifyingMap_unique hN hflat htest hr⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
