import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionCompactCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionDescent
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CoefficientExactness
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleIs
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCohomology

/-! # Denominators -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.Denominators.RationalProEtaleCoefficients

noncomputable section

/-! On a quasi-compact quasi-separated scheme, a power of ℓ times each actual rational degree-one class comes from integral cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology

private theorem overlap_to_base {Y T Z : Scheme.{0}} (g : Y ⟶ T) (u : Y ⟶ Z)
    (v : T ⟶ Z) (h : g ≫ v = u) :
    pullback.snd g g ≫ u = pullback.fst g g ≫ u := by
  rw [← h, ← Category.assoc, ← Category.assoc, pullback.condition]

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X]

theorem additiveH1_denominator (x : (ProEtaleCoefficients.RationalProEtaleCoefficients.additiveSheaf ℓ X).H 1) :
    ∃ N : ℕ, ∃ y : X.EllAdicCohomology ℓ 1,
      Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) 1 y = (ℓ ^ N) • x := by
  obtain ⟨E, rfl⟩ := Cohomology.ExtensionOf.CohomologyExtension.extension_exists X (ProEtaleCoefficients.RationalProEtaleCoefficients.additiveSheaf ℓ X) x
  obtain ⟨U, g, hU, hg, ⟨s⟩⟩ := E.exists_compact_cover_lift (⊤_ X.ProEt)
  let : IsAffine U.left := hU
  let : Surjective g.left := hg
  let : WeaklyEtale g.left := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover.Construction.proEtaleMorphism_weaklyEtale g
  let D : X.ProEt := Scheme.ProEt.mk (pullback.fst g.left g.left ≫ U.hom)
  let a : D ⟶ U := MorphismProperty.Over.homMk (pullback.fst g.left g.left) rfl
  let b : D ⟶ U := MorphismProperty.Over.homMk (pullback.snd g.left g.left) (by
    exact overlap_to_base g.left U.hom (⊤_ X.ProEt).hom (MorphismProperty.Over.w g))
  have : CompactSpace D.left :=
    inferInstanceAs (CompactSpace (pullback g.left g.left : Scheme.{0}))
  obtain ⟨c, hc, _⟩ := E.fiber_unique_difference D (E.restrict a s) (E.restrict b s)
  obtain ⟨N, t, ht⟩ := CoefficientExactness.RationalProEtaleCoefficients.sections_denominator ℓ X D c
  let π := cokernel.π (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)
  let f := (ℓ ^ N) • π
  have hz : f.hom.app (op D) c = 0 := by
    change (ℓ ^ N) • (π.hom.app (op D) c) = 0
    rw [← map_nsmul, ← ht]
    exact congrArg
      (fun k : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X ⟶ cokernel (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) =>
        k.hom.app (op D) t) (cokernel.condition (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X))
  have he := E.class_map_eq_zero_of_overlap f g a b (.of_hasPullback g.left g.left) s c hc hz
  change Sheaf.H.map ((ℓ ^ N) • π) 1 E.extClass = 0 at he
  rw [SheafCohomology.SheafCohomologyScalars.map_nsmul] at he
  obtain ⟨y, hy⟩ := CoefficientExactness.RationalProEtaleCoefficients.cohomology_lift_of_cokernel_zero ℓ X 1 ((ℓ ^ N) • E.extClass) he
  exact ⟨N, y, hy⟩

theorem rationalH1_denominator (x : IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X 1) :
    ∃ N : ℕ, ∃ y : X.EllAdicCohomology ℓ 1,
      ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X 1 y = (ℓ ^ N) • x := by
  obtain ⟨N, y, hy⟩ := additiveH1_denominator ℓ X (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X 1 x)
  refine ⟨N, y, (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X 1).injective ?_⟩
  change (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X 1)
      ((ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X 1).symm (Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) 1 y)) = _
  rw [AddEquiv.apply_symm_apply, map_nsmul]
  exact hy

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.Denominators.RationalProEtaleCoefficients
