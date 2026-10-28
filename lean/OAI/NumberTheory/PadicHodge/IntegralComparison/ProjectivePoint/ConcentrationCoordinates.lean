import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedPureConcentrationCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SupportedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineTerms

/-! # Concentration Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ConcentrationCoordinates

noncomputable section

/-! The original projective point concentration is exactly the
scalar-forgotten native concentration used by the global pure class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite

variable {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion i] (s : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s]
  (hs : s ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n + 2 ≤ B)

local instance projectiveSeparated : (Proj (homogeneousSubmodule (Fin (n+2)) R)).IsSeparated := by
  constructor
  rw [← terminal.comp_from (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))]
  infer_instance

abbrev nativeConcentration := by
  letI (q : ℕ) : ((Survivor.dual i s B).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc (Survivor.coefficient i s)
      (Survivor.chart (R := R)) B (n+2) hB q
  exact Global.PureSectionNormalization.concentration
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (Survivor.dual i s B) (n+1) (Survivor.exactAt i s hs B hB)

omit [Module.Injective R R] in
theorem concentration : SupportedClass.concentration i s hs B hB =
    nativeConcentration i s hs B hB := by
  let T := ProjectiveRefinement.Serre.fixedTower (Survivor.coefficient i s) B n (Fintype.card_fin (n+2))
  let (q : ℕ) : ((ProjectiveTower.PureDuality.dualComplex T n
      (Fintype.card_fin (n+2))).X q).IsQuasicoherent :=
    ProjectiveTower.PureDuality.term_quasicoherent T B n (Fintype.card_fin (n+2))
      (ProjectiveRefinement.Serre.fixed_above (Survivor.coefficient i s) B n (Fintype.card_fin (n+2))) hB q
  exact MixedPureConcentrationCoordinates.zero
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (Projective.TopTracePairing.canonicalTwist (R := R) n (Fintype.card_fin (n+2))) T.complex
    (n+1) (Survivor.exactAt i s hs B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ConcentrationCoordinates
