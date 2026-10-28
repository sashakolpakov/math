import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClopenNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothIntegralComponents
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ComponentSection
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSectionIso

/-! # Smooth To Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothToNormalization.Construction

noncomputable section

/-!
# Completion: smoothness of the map to relative normalization

For a proper smooth family with connected smooth proper total space over
a field, the component containing the diagonal of its self-base-change
normalizes to the total space. Its open immersion into the full
normalization realizes the graph of the normalization map as an open
immersion. The normalization map is therefore smooth.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p] [ConnectedSpace X]
  (f : X ⟶ Y) [IsProper f] [Smooth f]

/-- The graph of the actual normalization map over the original base. -/
def normalizationGraph : X ⟶ pullback f.fromNormalization f :=
  pullback.lift f.toNormalization (𝟙 X) (by simp)

include K p

/-- The graph of the actual normalization map is an open immersion after smooth self-base-change. -/
theorem proper_smooth_normalizationGraph_isOpenImmersion :
    IsOpenImmersion (normalizationGraph f) := by
  let q := pullback.snd f f
  let d := pullback.diagonal f
  have : IsNoetherian (pullback f f) := Proper.FiberComponents.Construction.properField_isNoetherian K (q ≫ p)
  let x : X := Nonempty.some inferInstance
  let U := Proper.FiberComponents.Construction.noetherianComponentOpen (pullback f f) (d x)
  have hU : IsClosed (U : Set (pullback f f : Scheme.{u})) := isClosed_connectedComponent
  have : IsIntegral U.toScheme := SmoothIntegralComponents.Construction.smooth_noetherian_component_isIntegral K (q ≫ p) (d x)
  let t := ComponentSection.Construction.schemeMapToComponent d x
  have ht : t ≫ (U.ι ≫ q) = 𝟙 X :=
    ComponentSection.Construction.schemeMapToComponent_section d x q (pullback.diagonal_snd f)
  have : IsIso (U.ι ≫ q).fromNormalization :=
    IntegralSectionIso.Construction.integralProperFamily_section_fromNormalization_isIso (U.ι ≫ q) t ht
  let c := ClopenNormalization.Construction.clopenNormalizationMap q U hU
  have : IsOpenImmersion c := ClopenNormalization.Construction.clopenNormalizationMap_isOpenImmersion q U hU
  let a : X ⟶ pullback f.fromNormalization f :=
    inv (U.ι ≫ q).fromNormalization ≫ c ≫ f.normalizationPullback f
  have : IsOpenImmersion a := by dsimp [a]; infer_instance
  have hi : inv (U.ι ≫ q).fromNormalization = t ≫ (U.ι ≫ q).toNormalization := by
    rw [← cancel_mono (U.ι ≫ q).fromNormalization]
    simp only [IsIso.inv_hom_id, Category.assoc, Scheme.Hom.toNormalization_fromNormalization, ht]
  have ha : a ≫ pullback.fst f.fromNormalization f = f.toNormalization := by
    dsimp only [a, c]
    rw [hi]
    simp only [Category.assoc]
    rw [ClopenNormalization.Construction.clopenNormalizationMap_toNormalization_assoc, ← Category.assoc,
      ComponentSection.Construction.schemeMapToComponent_ι]
    change d ≫ (pullback.snd f f).toNormalization ≫ f.normalizationPullback f ≫
      pullback.fst f.fromNormalization f = f.toNormalization
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst, ← Category.assoc,
      pullback.diagonal_fst, Category.id_comp]
  have has : a ≫ pullback.snd f.fromNormalization f = 𝟙 X := by
    dsimp only [a, c]
    simp only [Category.assoc, Scheme.Hom.normalizationPullback_snd]
    rw [ClopenNormalization.Construction.clopenNormalizationMap_fromNormalization, IsIso.inv_hom_id]
  have he : a = normalizationGraph f := by
    apply pullback.hom_ext
    · simpa only [normalizationGraph, pullback.lift_fst] using ha
    · simpa only [normalizationGraph, pullback.lift_snd] using has
  rw [← he]
  infer_instance

/-- The map to relative normalization of the actual proper smooth family is smooth. -/
theorem proper_smooth_toNormalization_smooth : Smooth f.toNormalization := by
  have := proper_smooth_normalizationGraph_isOpenImmersion K p f
  have he : normalizationGraph f ≫ pullback.fst f.fromNormalization f = f.toNormalization :=
    pullback.lift_fst _ _ _
  rw [← he]
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothToNormalization.Construction
