import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedQuasiFinite

/-! # Finite Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FiniteReduction

noncomputable section

/-! Finiteness of an actual etale map descends from a surjective
closed source reduction whose composite map is finite. The separated
diagonal is proved explicitly from the reduced diagonal. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X₀ X Y₀ Y : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
  (j : Y₀ ⟶ Y) [IsClosedImmersion j] [Surjective j]
  (f₀ : Y₀ ⟶ X₀) [IsFinite f₀] (f : Y ⟶ X) [Etale f]
  (h : j ≫ f = f₀ ≫ i)

private def productMap : pullback (f₀ ≫ i) (f₀ ≫ i) ⟶ pullback f f :=
  pullback.map _ _ _ _ j j (𝟙 X) ((Category.comp_id _).trans h.symm)
    ((Category.comp_id _).trans h.symm)

private instance productMap_closed : IsClosedImmersion (productMap i j f₀ f h) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance h.symm h.symm

omit [IsClosedImmersion i] [IsClosedImmersion j] [Surjective j] [IsFinite f₀] [Etale f] in
private theorem reduced_diagonal : j ≫ pullback.diagonal f =
    pullback.diagonal f₀ ≫ pullback.mapDesc f₀ f₀ i ≫ productMap i j f₀ f h := by
  apply pullback.hom_ext <;> simp [productMap]

include h in
omit [Etale f] in
theorem separated : IsSeparated f := by
  have hd : IsClosedImmersion (j ≫ pullback.diagonal f) := by
    rw [reduced_diagonal i j f₀ f h]
    infer_instance
  have hr : Set.range (j ≫ pullback.diagonal f) = Set.range (pullback.diagonal f) := by
    change Set.range (pullback.diagonal f ∘ j) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr j.surjective, Set.image_univ]
  exact ⟨IsClosedImmersion.of_isPreimmersion _
    (hr ▸ (j ≫ pullback.diagonal f).isClosedEmbedding.isClosed_range)⟩

include h in
theorem finite : IsFinite f := by
  let : IsSeparated f := separated i j f₀ f h
  let : IsFinite (j ≫ f) := h ▸ (inferInstance : IsFinite (f₀ ≫ i))
  let : UniversallyClosed f := UniversallyClosed.of_comp_surjective j f
  let : IsProper f := ⟨⟩
  let : LocallyQuasiFinite f := OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedQuasiFinite.locallyQuasiFinite_of_unramified f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FiniteReduction
