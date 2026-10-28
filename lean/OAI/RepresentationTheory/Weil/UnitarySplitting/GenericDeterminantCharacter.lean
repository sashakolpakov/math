import OAI.RepresentationTheory.Weil.UnitarySplitting.Generic
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorUnitary

/-! # Generic Determinant Character -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.GenericDeterminantCharacter.Construction

noncomputable section

/-! The determinant character correction is continuous on the generic
unitary domain and obeys the product-form discriminant identity. -/

open _root_.Matrix

def unitCharacterValue {E : Type} [NormedField E] (χ : Eˣ →ₜ* Circle) (x : E) : Circle := by
  classical
  exact if hx : x = 0 then 1 else χ (Units.mk0 x hx)

theorem unitCharacterValue_apply {E : Type} [NormedField E] (χ : Eˣ →ₜ* Circle) (x : E) (hx : x ≠ 0) :
    unitCharacterValue χ x = χ (Units.mk0 x hx) := by
  simp only [unitCharacterValue, dite_eq_right hx]

theorem unitCharacterValue_continuousOn {E : Type} [NormedField E] (χ : Eˣ →ₜ* Circle) :
    ContinuousOn (unitCharacterValue χ) {x : E | x ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : {x : E // x ≠ 0} => unitCharacterValue χ x.val)
  have hm : Continuous (fun x : {x : E // x ≠ 0} => Units.mk0 x.val x.property) :=
    Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val
  convert χ.continuous.comp hm using 1
  funext x
  exact unitCharacterValue_apply χ x.val x.property

def genericDeterminantCharacter
    {F E : Type} [Field F] [NormedField E] [Algebra F E]
    {I : Type} [Fintype I] [DecidableEq I]
    (σ : E ≃ₐ[F] E) (Q : Matrix I I E) (χ : Eˣ →ₜ* Circle) (g : DualPair.Construction.unitaryGroup σ Q) : Circle :=
  unitCharacterValue χ (TracePairing.Construction.unitaryDifferenceForm σ Q g).det

theorem genericDeterminantCharacter_continuousOn
    {F E : Type} [Field F] [NormedField E] [Algebra F E]
    {I : Type} [Fintype I] [DecidableEq I]
    (σ : E ≃ₐ[F] E) (Q : Matrix I I E) (hQ : Q.det ≠ 0) (χ : Eˣ →ₜ* Circle) :
    ContinuousOn (genericDeterminantCharacter σ Q χ) (Generic.Construction.unitaryGenericDomain σ Q) := by
  have hc : Continuous (fun g : DualPair.Construction.unitaryGroup σ Q => (TracePairing.Construction.unitaryDifferenceForm σ Q g).det) := by
    unfold TracePairing.Construction.unitaryDifferenceForm
    fun_prop
  exact (unitCharacterValue_continuousOn χ).comp hc.continuousOn (fun g hg => by
    change (TracePairing.Construction.unitaryDifferenceForm σ Q g).det ≠ 0
    rw [TensorUnitary.Construction.unitaryDifferenceForm_det]
    exact mul_ne_zero hQ hg)

theorem genericDeterminantCharacter_product
    {F E : Type} [Field F] [NormedField E] [Algebra F E]
    {I : Type} [Fintype I] [DecidableEq I]
    (σ : E ≃ₐ[F] E) (Q : Matrix I I E) (hQ : Q.det ≠ 0) (χ : Eˣ →ₜ* Circle)
    (g h : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q) (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    unitCharacterValue χ (CayleyProduct.Construction.unitaryProductForm σ Q g h).det =
      genericDeterminantCharacter σ Q χ g * genericDeterminantCharacter σ Q χ h *
        (genericDeterminantCharacter σ Q χ (g * h))⁻¹ := by
  have hn (a : DualPair.Construction.unitaryGroup σ Q) (ha : a ∈ Generic.Construction.unitaryGenericDomain σ Q) :
      (TracePairing.Construction.unitaryDifferenceForm σ Q a).det ≠ 0 := by rw [TensorUnitary.Construction.unitaryDifferenceForm_det]; exact mul_ne_zero hQ ha
  let Rg := Units.mk0 (TracePairing.Construction.unitaryDifferenceForm σ Q g).det (hn g hg)
  let Rh := Units.mk0 (TracePairing.Construction.unitaryDifferenceForm σ Q h).det (hn h hh)
  let Rgh := Units.mk0 (TracePairing.Construction.unitaryDifferenceForm σ Q (g * h)).det (hn (g * h) hgh)
  let S := Units.mk0 (CayleyProduct.Construction.unitaryProductForm σ Q g h).det
    (CayleyProduct.Construction.unitaryProductForm_nondegenerate σ Q hQ g h hg hh hgh)
  have hS : S * Rgh = Rg * Rh := by
    apply Units.ext
    exact TensorUnitary.Construction.unitaryProductForm_discriminant σ Q g h hgh
  have he : S = Rg * Rh * Rgh⁻¹ := eq_mul_inv_of_mul_eq hS
  simp only [genericDeterminantCharacter, unitCharacterValue_apply χ _ (hn g hg),
    unitCharacterValue_apply χ _ (hn h hh), unitCharacterValue_apply χ _ (hn (g * h) hgh),
    unitCharacterValue_apply χ _ (CayleyProduct.Construction.unitaryProductForm_nondegenerate σ Q hQ g h hg hh hgh)]
  change χ S = χ Rg * χ Rh * (χ Rgh)⁻¹
  rw [he, map_mul, map_mul, map_inv]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.GenericDeterminantCharacter.Construction
