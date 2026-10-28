import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.FrameScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates

/-! # Scalar Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarCoordinates

noncomputable section

/-! The original projective point scalar in coordinates with the
fixed section ideal and its intrinsic quotient, independent of equations. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Koszul.Comparison OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (z : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion z]
  (hbase : z ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (z ≫ f) ⁻¹ᵁ U)
  (i : Fin (n+2)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

abbrev line := ScalarFraction.line (R := R) (n := n)

local instance line_qc : (line (R := R) (n := n)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible (Survivor.chart (R := R)) (n+2))
include i hi in
theorem source_projective (q : ℕ) :
    Projective ((AffineOpen.InternalHom.sections U hU).obj ((Survivor.complex f z B).X q)) :=
  Affine.ProjectiveResolutionTerms.term_projective U hU i hi (Survivor.coefficient f z)
    (Survivor.chart (R := R)) B q
include hB in
theorem dual_qc (q : ℕ) :
    ((Affine.LinearResolutionPurity.internalComplex
      (line (R := R) (n := n)) (Survivor.complex f z B)).X q).IsQuasicoherent :=
  PrincipalConcentration.terms_qc f z B hB q
local instance sectionAlgebra : Algebra R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) U

def quotientIso : (AffineOpen.InternalHom.sections U hU).obj (Survivor.coefficient f z) ≅
    ModuleCat.of Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
      (Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) ⧸ (z ≫ f).ker.ideal ⟨U,hU⟩) :=
  (AffineOpen.InternalHom.sections U hU).mapIso (Closed.PointQuotientSquare.pointIso z f) ≪≫
    Closed.QuotientSectionNormalization.chartIso (z ≫ f) U hU

def quotient :
    (Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) ⧸ (z ≫ f).ker.ideal ⟨U,hU⟩) ≃ₐ[R] R :=
  SectionIdealQuotient.equiv R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) (z ≫ f)
    ((Category.assoc _ _ _).trans hbase) U hU hcontains

variable (e : Γ(line (R := R) (n := n), U) ≃ₗ[
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)]
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (z ≫ f).ker.ideal ⟨U,hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s t)))
  (y : (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t)
    (c+m)).obj (LocalCoordinates.principalDual f z B U hU))

omit [IsNoetherianRing R] in
theorem pointQuotient_factorization :
    Closed.PointQuotientSquare.pointQuotient z f U hU s t hst =
      quotientIso f z U hU ≪≫
        (Ideal.quotientEquivAlgOfEq Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
          hst.symm).toLinearEquiv.toModuleIso := by
  simp only [Closed.PointQuotientSquare.pointQuotient, quotientIso, Iso.trans_assoc]

omit [IsNoetherianRing R] in
theorem quotient_factorization :
    ScalarFraction.pointQuotient f z hbase U hU hcontains s t hst =
      (Ideal.quotientEquivAlgOfEq R
        ((KoszulPoint.Resolution.Comparison.full_ideal
          Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t).trans hst)).trans
        (quotient f z hbase U hU hcontains) :=
  SectionIdealQuotient.equations R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) (z ≫ f)
    ((Category.assoc _ _ _).trans hbase) U hU hcontains (Fin.append s t)
    ((KoszulPoint.Resolution.Comparison.full_ideal
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t).trans hst)

def value : R := by
  letI (q : ℕ) := source_projective f z B U hU i hi q
  letI (q : ℕ) := dual_qc f z B hB q
  exact PrincipalPoint.FrameScalar.value U hU
    (line (R := R) (n := n)) (Survivor.coefficient f z) (Survivor.complex f z B)
    (IntegralComparison.Projective.NegativeResolution.augmentation (Survivor.coefficient f z) (Survivor.chart (R := R)) B)
    ((z ≫ f).ker.ideal ⟨U,hU⟩) (quotientIso f z U hU) (quotient f z hbase U hU hcontains)
    e s t hreg hst (PrincipalPoint.Fraction.family U t) (n+1)
    (ScalarFraction.pure f z hbase B hB U hU)
    (ScalarFraction.zero f z hbase B hB U hU s t hst) y

def rawValue : R := by
  letI (q : ℕ) := source_projective f z B U hU i hi q
  letI (q : ℕ) := dual_qc f z B hB q
  exact KoszulPoint.ScalarCoordinates.scalar R
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU)
    (Principal.TerminalScalars.bijective U hU) (PrincipalPoint.Fraction.family U t) s t
    (PrincipalPoint.Koszul.Comparison.productCoordinates U hU (line (R := R) (n := n)) e
      (Survivor.coefficient f z) (Survivor.complex f z B)
      (IntegralComparison.Projective.NegativeResolution.augmentation (Survivor.coefficient f z) (Survivor.chart (R := R)) B)
      s t hreg (Closed.PointQuotientSquare.pointQuotient z f U hU s t hst))
    (n+1) (ScalarFraction.pure f z hbase B hB U hU)
    (ScalarFraction.zero f z hbase B hB U hU s t hst)
    (ScalarFraction.pointQuotient f z hbase U hU hcontains s t hst) y

theorem value_eq_raw : value f z hbase B hB U hU hcontains i hi e s t hst hreg y =
    rawValue f z hbase B hB U hU hcontains i hi e s t hst hreg y := by
  let (q : ℕ) := source_projective f z B U hU i hi q
  let (q : ℕ) := dual_qc f z B hB q
  exact congrArg₂
    (fun a b => KoszulPoint.ScalarCoordinates.scalar R
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU)
      (Principal.TerminalScalars.bijective U hU) (PrincipalPoint.Fraction.family U t) s t
      (PrincipalPoint.Koszul.Comparison.productCoordinates U hU (line (R := R) (n := n)) e
        (Survivor.coefficient f z) (Survivor.complex f z B)
        (IntegralComparison.Projective.NegativeResolution.augmentation (Survivor.coefficient f z) (Survivor.chart (R := R)) B)
        s t hreg a)
      (n+1) (ScalarFraction.pure f z hbase B hB U hU)
      (ScalarFraction.zero f z hbase B hB U hU s t hst) b y)
    (pointQuotient_factorization f z U hU s t hst).symm
    (quotient_factorization f z hbase U hU hcontains s t hst).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarCoordinates
