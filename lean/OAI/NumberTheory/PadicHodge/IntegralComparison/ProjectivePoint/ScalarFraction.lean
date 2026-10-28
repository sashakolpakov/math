import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.RefinedPointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedScalarCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionEquationQuotient

/-! # Scalar Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFraction

noncomputable section

/-! The unchanged fixed point resolution has a scalar-weighted mixed
fraction under its genuine projective common-refinement maps. The scalar
quotient is literal evaluation at the actual section. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (s₀ ≫ f) ⁻¹ᵁ U)
  (i : Fin (n+2)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (e : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (Survivor.chart (R := R)) (n+2), U) ≃ₗ[
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)] Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s =
    f.ker.ideal ⟨U, hU⟩)
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (s₀ ≫ f).ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn s))
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s t)))

local instance sectionAlgebra : Algebra R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) U

abbrev pointQuotient := SectionEquationQuotient.equiv R
  (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) (s₀ ≫ f)
  (by change (s₀ ≫ f) ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = 𝟙 _; exact (Category.assoc _ _ _).trans hbase) U hU hcontains (Fin.append s t)
  (SupportedLift.equations s₀ f U hU s t hst)

abbrev line := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (Survivor.chart (R := R) (n := n)) (n+2)

local instance line_qc : (line (R := R) (n := n)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible (Survivor.chart (R := R)) (n+2))

include hB in
theorem dual_terms_qc (q : ℕ) : ((Survivor.dual f s₀ B).X q).IsQuasicoherent :=
  PrincipalConcentration.terms_qc f s₀ B hB q

abbrev rightCoordinates := by
  let hr := KoszulMap.rightHomotopy s₀ f U hU i hi (Survivor.chart (R := R)) B
    (line (R := R) (n := n)) e s t hs hst hreg hregst
  exact KoszulPoint.HomCoordinates.homotopy Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (Principal.SectionPresheaf.rings U hU) s t _ _ _ hr

abbrev leftCoordinates := by
  let hl := KoszulLeft.leftHomotopy s₀ f U hU i hi (Survivor.chart (R := R)) B
    (line (R := R) (n := n)) e s hs hreg
  exact Koszul.NormalHomCoordinates.homotopy Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (Principal.SectionPresheaf.rings U hU) s _ _ _ hl

abbrev pure (q : ℕ) (hq : q ≠ n+1) := by
  letI (k : ℕ) := dual_terms_qc f s₀ B hB k
  exact Principal.ModuleHomology.exactAt U hU (Survivor.dual f s₀ B) q
    (Survivor.exactAt f s₀ hbase B hB q hq)

abbrev zero := by
  letI (k : ℕ) := dual_terms_qc f s₀ B hB k
  exact Principal.SupportedSurvivor.terms_zero (s₀ ≫ f) (Survivor.forms (R := R)) U hU
    (PrincipalPoint.Fraction.family U t)
    (PrincipalConcentration.parameters_outside f s₀ U hU s t hst)
    (Survivor.dual f s₀ B) (n+1) (Survivor.adjunctionIso f s₀ hbase B hB)

abbrev comparison := Koszul.RefinedScalarCoordinates.comparison
  Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU)
  (PrincipalPoint.Fraction.family U t) s t (PrincipalPoint.Fraction.units U hU t)
  _ _ _ _ _ (rightCoordinates f s₀ B U hU i hi e s t hs hst hreg hregst)
  (leftCoordinates f s₀ B U hU i hi e s hs hreg) R
  (Principal.TerminalScalars.bijective U hU) (n+1)
  (pure f s₀ hbase B hB U hU) (zero f s₀ hbase B hB U hU s t hst)
  (pointQuotient f s₀ hbase U hU hcontains s t hst)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFraction
