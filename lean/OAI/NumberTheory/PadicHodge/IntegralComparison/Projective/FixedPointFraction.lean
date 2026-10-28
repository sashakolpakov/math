import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ScalarPartialClass

/-! # Fixed Point Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FixedPointFraction

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
  (e : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (ProjectivePoint.Survivor.chart (R := R)) (n+2), U) ≃ₗ[
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

variable [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] (hcm : c+m=n+1)

abbrev normalization := ProjectivePoint.ScalarFraction.comparison
  f s₀ hbase B hB U hU hcontains i hi e s t hs hst hreg hregst
  (ProjectivePoint.LocalCoordinates.pointAt f s₀ hbase B hB U hU s t hst hcm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FixedPointFraction
