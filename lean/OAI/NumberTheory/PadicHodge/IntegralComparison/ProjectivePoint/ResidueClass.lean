import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FixedPointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedResidueClass

/-! # Residue Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClass

noncomputable section

/-! The original scalar point transfer maps to its literal closed-scheme
coefficient residue in supported cohomology. -/
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

abbrev comparison := by
  let W := PrincipalPoint.Fraction.family U t
  let hl := ScalarFraction.leftCoordinates f s₀ B U hU i hi e s hs hreg
  letI := Koszul.RefinedResidueClass.left_isIso
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU) W s _ _ _ hl (c+m)
  exact Koszul.RefinedResidueClass.actual_residue
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU)
    W s t (PrincipalPoint.Fraction.units U hU t) _ _ _ _
    (ScalarFraction.rightCoordinates f s₀ B U hU i hi e s t hs hst hreg hregst)
    R (Principal.TerminalScalars.bijective U hU) (n+1)
    (ScalarFraction.pure f s₀ hbase B hB U hU)
    (ScalarFraction.zero f s₀ hbase B hB U hU s t hst)
    (ScalarFraction.pointQuotient f s₀ hbase U hU hcontains s t hst)
    (Principal.ClosedKoszulResidue.target f U hU)
    (Principal.ClosedKoszulResidue.pullback f U hU s hs)
    (Principal.ClosedKoszulResidue.annihilated f U hU s hs) _ hl

variable [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] (hcm : c+m=n+1)

abbrev fixedPoint := comparison f s₀ hbase B hB U hU hcontains i hi e s t hs hst hreg hregst
  (LocalCoordinates.pointAt f s₀ hbase B hB U hU s t hst hcm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClass
