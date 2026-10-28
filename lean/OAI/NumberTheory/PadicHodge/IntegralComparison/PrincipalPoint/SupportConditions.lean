import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportConditions
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterSource

/-! # Support Conditions -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SupportConditions

noncomputable section

/-! The original point parameters retain exactly their support after
restriction to any affine neighborhood containing the whole section. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y Z T : Scheme.{0}} [Y.IsSeparated]
  (i : Y ⟶ Z) [IsAffineHom i] (s : T ⟶ Y) [IsClosedImmersion s]
  (U : Z.Opens) (hU : IsAffineOpen U)
  (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ i ⁻¹ᵁ U)
  (hcontains : ⊤ ≤ s ⁻¹ᵁ V)
  {g : ℕ} (t : Fin g → Γ(Z,U))
  (ht : Ideal.span (Set.range (fun j => i.app U (t j))) =
    s.ker.ideal ⟨i ⁻¹ᵁ U,hU.preimage i⟩)

include ht in
omit [Y.IsSeparated] [IsClosedImmersion s] in
theorem cover : (i ⁻¹ᵁ U) ⊓ SectionIdealPuncturedCover.outside s.ker =
    ⨆ j, i ⁻¹ᵁ Z.basicOpen (t j) := by
  simpa only [← Scheme.preimage_basicOpen] using
    SectionIdealPuncturedCover.cover s.ker (i ⁻¹ᵁ U) (hU.preimage i)
      (fun j => i.app U (t j)) ht

include hV hVU hcontains ht in
theorem conditions : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (PrincipalSource.OpenReindex.wideOpens i U hU)
    (PrincipalSource.OpenReindex.geometricOpens i U hU V)
    (Fraction.family U t)
    (SectionIdealPuncturedCover.outside s.ker)
    (SectionIdealPuncturedCover.outside s.ker) :=
  PrincipalSource.SupportConditions.conditions i U hU V hVU t hV
    (SectionIdealPuncturedCover.outside s.ker)
    (SectionIdealPuncturedCover.outside s.ker) le_rfl rfl
    (SectionIdealPuncturedCover.section_global V s hcontains)
    (SectionIdealPuncturedCover.section_global (i ⁻¹ᵁ U) s
      (hcontains.trans (s.preimage_mono hVU)))
    (cover i s U hU t ht)

end

namespace ProjectiveParameter
open _root_.MvPolynomial OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (s : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion s]
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.ParameterData X i s g U hU)
  (V : X.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ i.left ⁻¹ᵁ U)
  (hcontains : ⊤ ≤ s ⁻¹ᵁ V)

include hV hVU hcontains in
theorem conditions : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (PrincipalSource.OpenReindex.wideOpens i.left U hU)
    (PrincipalSource.OpenReindex.geometricOpens i.left U hU V)
    (Fraction.family U D.parameters)
    (SectionIdealPuncturedCover.outside s.ker)
    (SectionIdealPuncturedCover.outside s.ker) :=
  SupportConditions.conditions i.left s U hU V hV hVU hcontains
    D.parameters (ProjectivePoint.ParameterSource.span X i s g U hU D)

end ProjectiveParameter

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SupportConditions
