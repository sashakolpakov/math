import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothDualPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentratedSerre
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedDimension

/-! # Projective Serre -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSerre

noncomputable section

/-! Projective Serre duality descends to the genuine surviving
cohomology sheaf of a smooth closed subscheme's dual resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)
  (g : ℕ) [SmoothOfRelativeDimension g (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

abbrev source := Projective.InternalHomTotal.source
  (Projective.ClosedImmersionPurity.directImage f) B n hn

abbrev dualComplex := InternalHomCechTotal.internalComplex
  (Projective.TopTracePairing.canonicalTwist (R := R) n hn) (source f B n hn)

def dualizingSheaf := (dualComplex f B n hn).homology (n + 1 - g)

include hB in
theorem term_quasicoherent (q : ℕ) : ((dualComplex f B n hn).X q).IsQuasicoherent :=
  Projective.InternalHomCoherence.term (Projective.ClosedImmersionPurity.directImage f)
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB q

include hB in
theorem exactAt (q : ℕ) (hq : q ≠ n + 1 - g) : (dualComplex f B n hn).ExactAt q := by
  exact Projective.SmoothDualPurity.exactAt f (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn)
    B (n + 2) hB g q (by omega)

variable [Module.Injective R R] [Nonempty X]

def cohomologyIso (i : ℕ) (hi : i ≤ g) := by
  letI (q : ℕ) : ((dualComplex f B n hn).X q).IsQuasicoherent :=
    term_quasicoherent f B n hn hB q
  have hg : g ≤ n + 1 := by
    have hg' := ClosedDimension.projective f g
    omega
  exact ConcentratedSerre.Comparison.iso
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (Projective.TopTracePairing.canonicalTwist (R := R) n hn) (source f B n hn)
    (n + 1 - g) (exactAt f B n hn hB g) i
    (Projective.InternalHomTotal.serreIso (Projective.ClosedImmersionPurity.directImage f)
      B n hn hB (i + (n + 1 - g)) (by omega))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSerre
