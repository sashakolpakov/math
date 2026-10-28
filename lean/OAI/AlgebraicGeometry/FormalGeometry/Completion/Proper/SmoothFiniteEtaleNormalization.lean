import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizationComponentCover

/-! # Smooth Finite Etale Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SmoothFiniteEtaleNormalization.Construction

noncomputable section

/-!
# Completion: finite étale normalization of the entire proper smooth family

The total space may have multiple connected components. Their actual
normalizations cover the full normalization, and étaleness is local on
this source cover. Integrality of the full factor then makes it finite.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The actual normalization factor is finite étale, including for disconnected total space. -/
theorem proper_smooth_family_normalization_finite_etale (K : Type u) [Field K]
    {X Y : Scheme.{u}} [IsIntegral Y]
    (pX : X ⟶ Spec (CommRingCat.of K)) [IsProper pX] [Smooth pX]
    (pY : Y ⟶ Spec (CommRingCat.of K)) [Smooth pY]
    (f : X ⟶ Y) [IsProper f] [Smooth f] :
    IsFinite f.fromNormalization ∧ Etale f.fromNormalization := by
  have : IsNoetherian X := FiberComponents.Construction.properField_isNoetherian K pX
  have hE : Etale f.fromNormalization := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (NormalizationComponentCover.Construction.properComponentNormalizationCover f)]
    intro x
    let U := FiberComponents.Construction.noetherianComponentOpen X x
    let f' := NormalizationComponentCover.Construction.properComponentFamily f x
    have : IsIntegral U.toScheme := SmoothIntegralComponents.Construction.smooth_noetherian_component_isIntegral K pX x
    have : Smooth f' := by unfold f' NormalizationComponentCover.Construction.properComponentFamily; infer_instance
    have hc : IsClopen (Set.range f') :=
      ⟨f'.isClosedMap.isClosed_range, f'.isOpenMap.isOpen_range⟩
    have : Surjective f' := ⟨Set.range_eq_univ.mp (hc.eq_univ
      ⟨f' ⟨x, mem_connectedComponent⟩, ⟨x, mem_connectedComponent⟩, rfl⟩)⟩
    have h := (Finite.EtaleNormalization.Construction.proper_smooth_fromNormalization_finite_etale K (U.ι ≫ pX) pY f').2
    change Etale (NormalizationComponentCover.Construction.properComponentNormalizationMap f x ≫ f.fromNormalization)
    rw [NormalizationComponentCover.Construction.properComponentNormalizationMap_fromNormalization]
    exact h
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f.fromNormalization).mpr
    ⟨inferInstance, inferInstance⟩, hE⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SmoothFiniteEtaleNormalization.Construction
