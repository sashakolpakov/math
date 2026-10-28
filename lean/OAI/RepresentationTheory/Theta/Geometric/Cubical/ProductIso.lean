import OAI.RepresentationTheory.Theta.Geometric.Cubical.GaugeTransitions
import OAI.RepresentationTheory.Theta.Geometric.ProductGluing

/-! # Product Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.Cubical.ProductIso

noncomputable section

/-! The cubical regular units glue to an isomorphism of the actual
tensor products of original hyperplane pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem preimage_coordinateOverlap_le {X : Scheme} {n : ℕ} (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    {U V : X.Opens} {i j : Fin (n + 1)}
    (hU : U ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i)
    (hV : V ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j) :
    U ⊓ V ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i j := by
  rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
  exact le_inf (inf_le_left.trans hU) (inf_le_right.trans hV)

theorem cubical_thetaProduct_iso
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonTripleCube hJ).projectiveDimension))
    (e : Φ.triple.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonTripleCube hJ).projectiveDimension
        ((F.commonTripleCube hJ).projectiveMap t))
    (fP : Fin 4 → (X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension)))
    (fN : Fin 3 → (X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension)))
    (heP : ∀ k z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fP k) (e (QuotientAddGroup.mk z)) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
        (F.projectiveMap (QuotientAddGroup.mk (Φ.cubePositiveArgument k z))))
    (heN : ∀ k z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fN k) (e (QuotientAddGroup.mk z)) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
        (F.projectiveMap (QuotientAddGroup.mk (Φ.cubeNegativeArgument k z)))) :
    Nonempty (ProductFrames.thetaProductModule (fun k => (fN k).left) ≅ ProductFrames.thetaProductModule (fun k => (fP k).left)) := by
  let U := fun p : (Fin 4 → Fin (F.projectiveDimension + 1)) ×
    (Fin 3 → Fin (F.projectiveDimension + 1)) => ComparisonGauges.cubicalGaugeOpen F hJ f p.1 p.2
  have hU : iSup U = ⊤ := by
    rw [iSup_prod]
    exact ComparisonGauges.cubicalGaugeOpen_cover F hJ f e he hsurj
  have hUP : ∀ p k, U p ≤ (fP k).left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) (p.1 k) :=
    fun p k => GaugeTransitions.cubicalGaugeOpen_le_positive F hJ f e hsurj he fP heP p.1 p.2 k
  have hUN : ∀ p k, U p ≤ (fN k).left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) (p.2 k) :=
    fun p k => GaugeTransitions.cubicalGaugeOpen_le_negative F hJ f e hsurj he fN heN p.1 p.2 k
  have hWP := fun p q k => preimage_coordinateOverlap_le (fP k).left (hUP p k) (hUP q k)
  have hWN := fun p q k => preimage_coordinateOverlap_le (fN k).left (hUN p k) (hUN q k)
  apply ProductGluing.thetaProduct_iso_of_comparison_gauges (fun k => (fP k).left) (fun k => (fN k).left)
    U hU hUP hUN (fun p => ComparisonGauges.cubicalGaugeUnit F hJ f p.1 p.2) hWP hWN
  intro p q
  exact GaugeTransitions.cubicalGaugeUnit_transition F hJ f e hsurj he fP fN heP heN p.1 q.1 p.2 q.2
    (U p ⊓ U q) inf_le_left inf_le_right (hWP p q) (hWN p q)

end

end OAI.RepresentationTheory.Theta.Geometric.Cubical.ProductIso
