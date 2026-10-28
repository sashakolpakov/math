import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedSurvivor
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SupportedLift

/-! # Principal Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PrincipalConcentration

noncomputable section

/-! The original fixed point resolution has its canonical support
concentration on the actual parameter principal diagram. The explicit
duplicate-parameter Koszul lift has exactly that survivor coordinate. -/
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
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (s₀ ≫ f).ker.ideal ⟨U, hU⟩)

attribute [local instance] Survivor.coefficient_qc
  Survivor.coefficient_finite

include hB in
theorem terms_qc (q : ℕ) : ((Survivor.dual f s₀ B).X q).IsQuasicoherent :=
  Projective.InternalHomCoherence.term (Survivor.coefficient f s₀) (Survivor.chart (R := R)) B (n+2) hB q

include hst in
omit [IsNoetherianRing R] [IsClosedImmersion f] [IsClosedImmersion s₀] in
theorem parameters_outside (i : ULift.{u} (Fin m)) :
    Principal.SectionPresheaf.openSubset U (PrincipalPoint.Fraction.family U t i) ≤
      SectionIdealPuncturedCover.outside (s₀ ≫ f).ker := by
  have hspan : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ f).ker.ideal ⟨U, hU⟩ := by
    rw [KoszulPoint.Ideal.append] at hst
    exact hst
  change (Proj (homogeneousSubmodule (Fin (n+2)) R)).basicOpen (t i.down) ≤ _
  simpa only [Fin.append_right] using SectionIdealPuncturedCover.basicOpen_le
    (s₀ ≫ f).ker U hU (Fin.append s t) hspan (Fin.natAdd c i.down)

abbrev concentration := by
  letI (q : ℕ) := terms_qc f s₀ B hB q
  exact Principal.SupportedSurvivor.concentration U hU
    (PrincipalPoint.Fraction.family U t) (Survivor.dual f s₀ B) (n+1)
    (Survivor.exactAt f s₀ hbase B hB)

abbrev lift_normalization := by
  letI (q : ℕ) := terms_qc f s₀ B hB q
  exact Principal.SupportedSurvivor.lift_normalization
    (s₀ ≫ f) (Survivor.forms (R := R)) U hU (PrincipalPoint.Fraction.family U t)
    (parameters_outside f s₀ U hU s t hst) (Survivor.dual f s₀ B) (n+1)
    (Survivor.adjunctionIso f s₀ hbase B hB) (Survivor.exactAt f s₀ hbase B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PrincipalConcentration
