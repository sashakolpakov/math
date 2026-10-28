import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.PointKoszulMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientIdentity

/-! # Point Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.PointFraction

noncomputable section

/-! Actual projective coefficient maps evaluated on a normal-quotient
vector give the mixed fraction with the unchanged fixed-point scalar. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (M : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType]
  (v : M ⟶ ProjectivePoint.KoszulMap.point s₀ f)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (s₀ ≫ f) ⁻¹ᵁ U)
  (i : Fin (n+2)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (e : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (ProjectivePoint.Survivor.chart (R := R)) (n+2), U) ≃ₗ[
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)]
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (s₀ ≫ f).ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn s))
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s t)))
  (T : ModuleCat.{u} Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T) (PM : ProjectiveResolution T)

local instance sectionAlgebra : Algebra R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) U

local instance line_qc : (ProjectivePoint.ScalarFraction.line (R := R) (n := n)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible (ProjectivePoint.Survivor.chart (R := R)) (n+2))

abbrev coefficient := PointKoszulMap.coefficient s₀ f M v U hU s t hst T eM
abbrev pointLift := PointKoszulMap.pointLift s₀ f M v U hU s t hst hregst T eM PM

abbrev rightCoordinates := PointKoszulMap.rightCoordinates
  s₀ f M v U hU i hi (ProjectivePoint.Survivor.chart (R := R)) B
  (ProjectivePoint.ScalarFraction.line (R := R) (n := n)) e s t hst hregst T eM PM

abbrev leftCoordinates := by
  let h := PointKoszulMap.leftHomotopy s₀ f M v U hU i hi
    (ProjectivePoint.Survivor.chart (R := R)) B (ProjectivePoint.ScalarFraction.line (R := R) (n := n)) e T eM PM
  exact HomCoefficientIdentity.Functor.identityHomotopy
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.LineFrame.scalars U hU)
    PM.complex _ _ _ h

variable (β : ModuleCat.of Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) ⧸ KoszulPartial.Resolution.normalIdeal _ s) ⟶ T)
  (w : Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hw : β ≫ coefficient f s₀ M v U hU s t hst T eM = w • KoszulPartial.Resolution.quotient _ s t)

abbrev vectorLift := ProjectiveResolution.lift β (KoszulPartial.Resolution.normalResolution _ s hreg) PM

abbrev evaluation := Koszul.CoefficientEvaluationHomotopy.evaluation
  Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU) s hreg T PM
    (vectorLift U s hreg T PM β)

abbrev evaluationHomotopy := Koszul.CoefficientEvaluationHomotopy.homotopy
  Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU) s t hreg hregst T PM
  (coefficient f s₀ M v U hU s t hst T eM) β
  (pointLift f s₀ M v U hU s t hst hregst T eM PM) (vectorLift U s hreg T PM β)
  (ProjectiveResolution.lift_commutes (coefficient f s₀ M v U hU s t hst T eM)
    PM (KoszulPartial.Resolution.pointResolution _ s t hregst))
  (ProjectiveResolution.lift_commutes β (KoszulPartial.Resolution.normalResolution _ s hreg) PM) w hw

abbrev comparison := Koszul.RefinedCoefficientCoordinates.comparison
  Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU)
  (PrincipalPoint.Fraction.family U t) s t (PrincipalPoint.Fraction.units U hU t)
  _ _ _ _ _ _ (evaluation U hU s hreg T PM β)
  (rightCoordinates f s₀ B M v U hU i hi e s t hst hregst T eM PM)
  (leftCoordinates f s₀ B M v U hU i hi e T eM PM)
  w (evaluationHomotopy f s₀ M v U hU s t hst hreg hregst T eM PM β w hw)
  R (Principal.TerminalScalars.bijective U hU) (n+1)
  (ProjectivePoint.ScalarFraction.pure f s₀ hbase B hB U hU)
  (ProjectivePoint.ScalarFraction.zero f s₀ hbase B hB U hU s t hst)
  (ProjectivePoint.ScalarFraction.pointQuotient f s₀ hbase U hU hcontains s t hst)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.PointFraction
