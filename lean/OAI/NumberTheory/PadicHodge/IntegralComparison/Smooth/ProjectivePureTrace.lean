import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSerre
import OAI.NumberTheory.PadicHodge.IntegralComparison.ArtinianCechStructureUnit

/-! # Projective Pure Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePureTrace

noncomputable section

/-! The pure Serre trace is evaluated on the actual constant function
one. For a pointed, proper, smooth, geometrically connected family over
an Artinian local ring, this trace is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} [Nonempty X]
  (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)
  (g : ℕ) [SmoothOfRelativeDimension g (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  (s : Spec (.of R) ⟶ X) (hs : s ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _)

def pairing := by
  have hg : g ≤ n + 1 := by
    have h := ClosedDimension.projective f g
    omega
  exact Projective.PureTrace.pairing (Projective.ClosedImmersionPurity.directImage f)
    B n hn hB (n + 1 - g) (ProjectiveSerre.exactAt f B n hn hB g) g (by omega)

def trace :=
  SerreUnitTrace.trace (Projective.TopTracePairing.coefficientRing R) (pairing f B n hn hB g)
    (Cech.StructureUnit.unit f (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ)))

def traceIso := by
  let : Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := SmoothOfRelativeDimension.smooth g _
  exact SerreUnitTrace.traceIso (Projective.TopTracePairing.coefficientRing R) (pairing f B n hn hB g)
    (ArtinianCechStructureUnit.iso f (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) s hs
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))).toLinearEquiv

theorem traceIso_hom : (traceIso f B n hn hB g s hs).hom = trace f B n hn hB g := by
  let : Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := SmoothOfRelativeDimension.smooth g _
  exact (SerreUnitTrace.traceIso_hom (Projective.TopTracePairing.coefficientRing R) (pairing f B n hn hB g)
    (ArtinianCechStructureUnit.iso f (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) s hs
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))).toLinearEquiv).trans
    (congrArg (SerreUnitTrace.trace (Projective.TopTracePairing.coefficientRing R) (pairing f B n hn hB g))
      (ArtinianCechStructureUnit.iso_one f (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) s hs
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePureTrace
