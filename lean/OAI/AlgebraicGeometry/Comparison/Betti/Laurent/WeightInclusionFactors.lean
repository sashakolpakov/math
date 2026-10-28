import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentOrderedFactors
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeightComponents

/-! # Weight Inclusion Factors -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.WeightInclusionFactors.Dolbeault

noncomputable section

/-! The original fixed-weight inclusion has the expected monomial in every allowed factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Scheme.Modules

universe u

variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]

theorem algebraicLaurentWeightInclusion_factor (d : ℤ)
    (e : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) (q : ℕ)
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) q)
    (he : e.IsAllowedOn (fun k => (a.val k).down))
    (s : SheafCohomology.Projective.OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (CommRingCat.of R), ⊤)
      e.liftedNegativeSupport q) :
    Projective.LaurentOrderedFactors.Dolbeault.algebraicHomogeneousLaurentFactorProjection (R := R) d q a
      (SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e q s) =
        AddMonoidAlgebra.single ⟨e, he⟩ (s.val a) := by
  classical
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro f
  have h := SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
    (R := R) d f.val a f.property
    (SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e q s)
  change (SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent (R := R) d f.val q
      (SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e q s)).val a =
    (Projective.LaurentOrderedFactors.Dolbeault.algebraicHomogeneousLaurentFactorProjection (R := R) d q a
      (SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e q s)).coeff f at h
  rw [← h]
  by_cases hf : f.val = e
  · have hf' : f = ⟨e, he⟩ := Subtype.ext hf
    subst f
    rw [SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_inclusion]
    simp
  · rw [SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_inclusion_ne (R := R) d e f.val hf]
    have hf' : (⟨e, he⟩ : {v : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      v.IsAllowedOn (fun k => (a.val k).down)}) ≠ f := by
      intro hfe
      exact hf (congrArg Subtype.val hfe).symm
    simp [hf']

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.WeightInclusionFactors.Dolbeault
