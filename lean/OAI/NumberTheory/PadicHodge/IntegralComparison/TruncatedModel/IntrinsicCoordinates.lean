import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TransportedPrincipalData
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SameSupportIntrinsic

/-! # Intrinsic Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCoordinates.IntrinsicComparison

noncomputable section

/-! The selected-source and same-support recovery maps are the literal
native principal comparison used by the bounded fraction formula. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Z : Scheme.{0}} (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  (U : Z.Opens) (hU : IsAffineOpen U) (t : Fin g → Γ(Z,U))
  (c : ℕ) {μ : Type} [LinearOrder μ] (A : μ → X.left.Opens)
  (hA : iSup A = ⊤) (haA : ∀ j, IsAffineOpen (A j))

abbrev form := TopCover.form p k n X g
local instance form_qc : (form p k n X g).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X g

section Selected
variable {T : Scheme.{0}} (f : X.left ⟶ T) (i : T ⟶ Z) [IsAffineHom (f ≫ i)]
  (z : Γ(X.left,(f ≫ i) ⁻¹ᵁ U)) (O₁ O₂ : X.left.Opens)
  (H : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (PrincipalSource.OpenReindex.wideOpens (f ≫ i) U hU)
    (PrincipalSource.OpenReindex.geometricOpens (f ≫ i) U hU (X.left.basicOpen z))
    (PrincipalPoint.Fraction.family U t) O₁ O₂)
  (hza : IsAffineOpen (X.left.basicOpen z)) (hZU : X.left.basicOpen z ≤ (f ≫ i) ⁻¹ᵁ U)

omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] [IsAffineHom (f ≫ i)] in
theorem selected : PrincipalSource.IntrinsicRecovery.Intrinsic.nativeComparison f i U hU t
    (form p k n X g) z O₁ O₂ H hza hZU c g A hA haA =
    TransportedPrincipalData.Fraction.nativeComparison p k n X (f ≫ i) U hU
      ⟨X.left.basicOpen z,hza⟩ hZU g t O₂ A hA haA H.selected.wide_affine
      H.selected.wide_punctured H.selected.wide_cover H.selected.wide_global c := rfl
end Selected

variable (π : X.left ⟶ Z) [IsAffineHom π] (V : X.left.affineOpens)
  (hVU : V.val ≤ π ⁻¹ᵁ U) (O : X.left.Opens)
  (H : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (PrincipalSource.OpenReindex.wideOpens π U hU)
    (PrincipalSource.OpenReindex.geometricOpens π U hU V.val)
    (PrincipalPoint.Fraction.family U t) O O)

omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] [IsAffineHom π] in
theorem same : Principal.SameSupportIntrinsic.Intrinsic.nativeComparison π U hU V.val V.property hVU t O H
    (form p k n X g) c (g+c) A hA haA =
    TransportedPrincipalData.Fraction.nativeComparison p k n X π U hU V hVU g t O
      A hA haA H.selected.wide_affine H.selected.wide_punctured H.selected.wide_cover
      H.selected.wide_global c := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCoordinates.IntrinsicComparison
