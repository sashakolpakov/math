import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIndexedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitPureClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineTerms

/-! # Unit Concentration Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitConcentrationCoordinates

noncomputable section

/-! The unchanged projective unit-class concentration is the indexed
native Čech concentration, with its original degree cast. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (B n : ℕ) (hn : Fintype.card σ=n+2) (hB : n+2≤B)
  (c : ℕ) (hM : ∀ q, q ≠ c → (ProjectiveRefinement.Serre.fixedDual M B n hn).ExactAt q)
  (g : ℕ) (hg : g+c=n+1)
local instance projectiveSeparated : (Proj (homogeneousSubmodule σ R)).IsSeparated := by
  constructor
  rw [← terminal.comp_from (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))]
  infer_instance

abbrev native := by
  letI : ∀ q : ℕ, ((ProjectiveRefinement.Serre.fixedDual M B n hn).X q).IsQuasicoherent :=
    fun q => ProjectiveRefinement.AffineTerms.fixed_dual_qc M
      (NegativeTwistResidueNaturality.topChart.{u} (n+1) hn) B (n+2) hB q
  exact Global.PureIndexedCoordinates.concentration
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (ProjectiveRefinement.Serre.fixedDual M B n hn) c hM g (n+1) hg.symm

omit [Module.Injective R R] in
theorem concentration :
    UnitPureClass.concentration M B n hn hB c hM g hg =
      native M B n hn hB c hM g hg := by
  let T := ProjectiveRefinement.Serre.fixedTower M B n hn
  let : ∀ q : ℕ, ((ProjectiveTower.PureDuality.dualComplex T n hn).X q).IsQuasicoherent :=
    fun q => ProjectiveTower.PureDuality.term_quasicoherent T B n hn
      (ProjectiveRefinement.Serre.fixed_above M B n hn) hB q
  exact Global.PureIndexedCoordinates.internalHom
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) c
    (TopTracePairing.canonicalTwist (R := R) n hn) T.complex hM g (n+1) hg.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitConcentrationCoordinates
