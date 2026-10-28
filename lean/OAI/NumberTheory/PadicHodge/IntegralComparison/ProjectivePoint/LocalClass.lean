import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SupportedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SupportedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PrincipalConcentration

/-! # Local Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalClass

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

local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor.dual f s₀ B
local notation "W" => OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction.family U t
local notation "hW" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PrincipalConcentration.parameters_outside f s₀ U hU s t hst

abbrev concentratedIso (q : ℕ) := by
  letI (k : ℕ) := PrincipalConcentration.terms_qc f s₀ B hB k
  exact PrincipalReference.SupportedClass.Reference.concentratedIso U hU W D (n+1)
    (Survivor.exactAt f s₀ hbase B hB) q

abbrev localize (q : ℕ) := by
  letI (k : ℕ) := PrincipalConcentration.terms_qc f s₀ B hB k
  exact PrincipalReference.SupportedClass.Reference.localize U hU W D (n+1)
    (Survivor.exactAt f s₀ hbase B hB) (s₀ ≫ f) (Survivor.forms (R := R))
      (Survivor.adjunctionIso f s₀ hbase B hB) hW q

abbrev localize_concentrated (q : ℕ) := by
  letI (k : ℕ) := PrincipalConcentration.terms_qc f s₀ B hB k
  exact PrincipalReference.SupportedClass.Reference.localize_concentrated U hU W D (n+1)
    (Survivor.exactAt f s₀ hbase B hB) (s₀ ≫ f) (Survivor.forms (R := R))
      (Survivor.adjunctionIso f s₀ hbase B hB) hW q

def globalCoordinate :=
  (SupportedClass.concentration f s₀ hbase B hB).hom ≫
    (SupportedClass.globalIso f s₀ B).inv

def map := globalCoordinate f s₀ hbase B hB ≫ localize f s₀ hbase B hB U hU s t hst (n+1)

abbrev map_concentrated := congrArg (fun a => globalCoordinate f s₀ hbase B hB ≫ a)
  (localize_concentrated f s₀ hbase B hB U hU s t hst (n+1))

variable [IsArtinianRing R] [IsLocalRing R]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

abbrev pointClass := map f s₀ hbase B hB U hU s t hst
  (SupportedClass.fixedPointClass f s₀ hbase B hB)

abbrev pointClass_normalization := ConcreteCategory.congr_hom
  (map_concentrated f s₀ hbase B hB U hU s t hst)
    (SupportedClass.fixedPointClass f s₀ hbase B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalClass
