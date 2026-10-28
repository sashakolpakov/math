import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence

/-! # Local Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates

noncomputable section

/-! The original fixed trace class localized to its actual principal
supported diagram. Both the point resolution and its trace are unchanged. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (s₀ ≫ f).ker.ideal ⟨U, hU⟩)

variable [IsArtinianRing R] [IsLocalRing R]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

abbrev principalDual := ((Principal.ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj
  (Survivor.dual f s₀ B)

def pointAt (hcm : c+m=n+1) :
    (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t) (c+m)).obj
      (principalDual f s₀ B U hU) := by
  rw [hcm]
  exact LocalClass.pointClass f s₀ hbase B hB U hU s t hst

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates
