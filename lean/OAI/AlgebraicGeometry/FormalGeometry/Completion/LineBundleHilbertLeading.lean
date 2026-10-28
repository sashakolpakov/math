import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleInjections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialComparison

/-! # Line Bundle Hilbert Leading -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleHilbertLeading

noncomputable section

/-! Every actual line bundle on an integral closed projective scheme
has the same Hilbert-polynomial degree and leading coefficient as its structure sheaf. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

theorem lineBundle_hilbert_degree_leadingCoeff (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    letI : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
    letI : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
    letI : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
    letI : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f L.sheaf j).natDegree =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) j).natDegree ∧
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f L.sheaf j).leadingCoeff =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) j).leadingCoeff := by
  let : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  let : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  let : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  obtain ⟨n, hn⟩ := Projective.LineBundleInjections.Construction.closedProjectiveLineBundle_eventually_injections f L j
  obtain ⟨a, c, ha, hc⟩ := hn n le_rfl
  have : Mono a := ha
  have : Mono c := hc
  let H := (Scheme.Modules.pullback f).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n)
  let e : ClosedHilbertNumerics.Construction.closedProjectiveTwist f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) j n ≅ H :=
    ((Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.unitIso X).symm ⊗ᵢ Iso.refl H) ≪≫ λ_ H
  let c' : L.sheaf ⟶ ClosedHilbertNumerics.Construction.closedProjectiveTwist f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) j n := c ≫ e.inv
  obtain ⟨b₁, hb₁⟩ := ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_eventually_le_of_mono f
    (N := ClosedHilbertNumerics.Construction.closedProjectiveTwist f L.sheaf j n) a j
  obtain ⟨b₂, hb₂⟩ := ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_eventually_le_of_mono f c' j
  apply PolynomialComparison.Construction.polynomial_degree_leadingCoeff_eq_of_mutual_shift_bounds _ _
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_leadingCoeff_pos f L.sheaf j (GeneratedLineBundleFrames.Construction.lineBundle_not_isZero L))
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_leadingCoeff_pos f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) j
      (GeneratedLineBundleFrames.Construction.lineBundle_not_isZero (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X))) (max b₁ b₂) n
  · intro m hm
    simpa only [ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_twist, Polynomial.taylor_eval] using
      hb₂ m ((le_max_right _ _).trans hm)
  · intro m hm
    simpa only [ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_twist, Polynomial.taylor_eval] using
      hb₁ m ((le_max_left _ _).trans hm)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleHilbertLeading
