import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ClosedPoint
import OAI.NumberTheory.PadicHodge.IntegralComparison.CommonSectionPrincipalNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SectionPuncture

/-! # Common Point Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Genuine principal neighborhoods of the two original identity
sections with exactly the same open in the common special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)
  (U₁ : (A.truncatedShiftModel n m hm).left.affineOpens)
  (U₂ : (A.truncatedModel n).scheme.left.affineOpens)
  (h₁ : ⊤ ≤ A.truncatedShiftIdentitySection n m hm ⁻¹ᵁ U₁.val)
  (h₂ : ⊤ ≤ A.truncatedIdentitySection n ⁻¹ᵁ U₂.val)

include h₁ h₂ in
theorem Geometry.AbelianH1Model.exists_truncatedShiftCommonPointNeighborhood :
    ∃ a₁ : Γ((A.truncatedShiftModel n m hm).left, U₁.val),
    ∃ a₂ : Γ((A.truncatedModel n).scheme.left, U₂.val),
      (⊤ ≤ A.truncatedShiftIdentitySection n m hm ⁻¹ᵁ
        (A.truncatedShiftModel n m hm).left.basicOpen a₁) ∧
      (⊤ ≤ A.truncatedIdentitySection n ⁻¹ᵁ (A.truncatedModel n).scheme.left.basicOpen a₂) ∧
      A.truncatedShiftReduction n m hm ⁻¹ᵁ (A.truncatedShiftModel n m hm).left.basicOpen a₁ =
        A.truncatedReduction n ⁻¹ᵁ (A.truncatedModel n).scheme.left.basicOpen a₂ := by
  let : Subsingleton (Spec (CommRingCat.of (ZMod q))) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum (ZMod q)
  exact IntegralComparison.CommonSectionPrincipalNeighborhood.exists_principal
    (Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)))
    (IntegralComparison.Truncated.SectionPuncture.reduction_surjective q (ZMod q) n)
    A.specialIdentitySection (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedIdentitySection n)
    (A.truncatedShiftIdentitySection_reduction n m hm).symm
    (A.truncatedIdentitySection_reduction n)
    U₁.val U₂.val U₁.property U₂.property h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
