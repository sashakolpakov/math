import OAI.RepresentationTheory.Theta.Geometric.CoordinatePoleIso
import OAI.RepresentationTheory.Theta.Geometric.CoordinatePoleNonvanishing
import OAI.RepresentationTheory.Theta.Geometric.LineSectionNonvanishingPullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Hyperplane Pullback Ampleness -/

namespace OAI.RepresentationTheory.Theta.Geometric.HyperplanePullbackAmpleness

noncomputable section

/-! The hyperplane pullback along an affine morphism from a quasi-compact
scheme is ample, using the actual coordinate-section affine cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem hyperplanePullback_isAmple {X : Scheme} [CompactSpace X] {n : ℕ}
    (f : X ⟶ OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) [IsAffineHom f] :
    (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1)).IsAmple := by
  let L := OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1)
  refine ⟨isCompact_univ, fun x => ?_⟩
  have hc : f x ∈ ⨆ j : Fin (n + 1), OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j := by
    rw [OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  obtain ⟨e⟩ := CoordinatePoleIso.coordinatePole_iso_twist n j
  let P := AlgebraicHyperplaneBundle.lineBundleOfInvertible (OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := ℂ) j)
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf_isInvertible j)
  let s : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf :=
    OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleUnitHom (R := ℂ) j) ≫
      ((Scheme.Modules.pullback f).mapIso e).hom
  have hs : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = f ⁻¹ᵁ OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j := by
    apply (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso _ ((Scheme.Modules.pullback f).mapIso e)).trans
    exact (LineSectionNonvanishingPullback.lineSectionNonvanishing_pullback f P
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleUnitHom (R := ℂ) j)).trans
      (congrArg (fun U => f ⁻¹ᵁ U) (CoordinatePoleNonvanishing.coordinatePoleSection_nonvanishing n j))
  refine ⟨1, Nat.zero_lt_one, L, OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one _, s, ?_, ?_⟩
  · rw [hs]
    exact hj
  · rw [hs]
    exact (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := ℂ) j).preimage f

end

end OAI.RepresentationTheory.Theta.Geometric.HyperplanePullbackAmpleness
