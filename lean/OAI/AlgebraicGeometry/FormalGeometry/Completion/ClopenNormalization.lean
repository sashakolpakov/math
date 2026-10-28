import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Normalization

/-! # Clopen Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ClopenNormalization.Construction

noncomputable section

/-!
# Completion: normalization preserves an actual open-and-closed component

The component inclusion induces an open immersion of relative
normalizations by the coproduct universal property.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
  (U : X.Opens) (hU : IsClosed (U : Set X))

include hU

theorem clopen_ι_isClosedImmersion : IsClosedImmersion U.ι := by
  apply IsClosedImmersion.of_isPreimmersion
  simpa only [Scheme.Opens.range_ι] using hU

/-- The induced map from the component's normalization into the full normalization. -/
def clopenNormalizationMap :
    letI := clopen_ι_isClosedImmersion U hU
    (U.ι ≫ f).normalization ⟶ f.normalization := by
  let := clopen_ι_isClosedImmersion U hU
  exact (U.ι ≫ f).normalizationDesc (U.ι ≫ f.toNormalization) f.fromNormalization (by simp)

/-- Normalization maps an open-and-closed component by an open immersion. -/
theorem clopenNormalizationMap_isOpenImmersion :
    letI := clopen_ι_isClosedImmersion U hU
    IsOpenImmersion (clopenNormalizationMap f U hU) := by
  let := clopen_ι_isClosedImmersion U hU
  let V : X.Opens := ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩
  have : IsClosedImmersion V.ι := clopen_ι_isClosedImmersion V U.isOpen.isClosed_compl
  obtain ⟨H⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl U.ι V.ι (by
    simp [isCompl_iff, disjoint_iff, codisjoint_iff, V, SetLike.ext'_iff])
  have he : clopenNormalizationMap f U hU = coprod.inl ≫ (f.normalizationCoprodIso H).hom := by
    simp [clopenNormalizationMap, Scheme.Hom.normalizationCoprodIso]
  rw [he]
  infer_instance

@[reassoc]
theorem clopenNormalizationMap_toNormalization :
    letI := clopen_ι_isClosedImmersion U hU
    (U.ι ≫ f).toNormalization ≫ clopenNormalizationMap f U hU = U.ι ≫ f.toNormalization := by
  let := clopen_ι_isClosedImmersion U hU
  exact (U.ι ≫ f).toNormalization_normalizationDesc _ _ (by simp)

@[reassoc]
theorem clopenNormalizationMap_fromNormalization :
    letI := clopen_ι_isClosedImmersion U hU
    clopenNormalizationMap f U hU ≫ f.fromNormalization = (U.ι ≫ f).fromNormalization := by
  let := clopen_ι_isClosedImmersion U hU
  exact (U.ι ≫ f).normalizationDesc_comp _ _ (by simp)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ClopenNormalization.Construction
