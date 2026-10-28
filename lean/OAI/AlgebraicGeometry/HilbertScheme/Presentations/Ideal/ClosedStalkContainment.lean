import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ClosedStalkDetection

/-! # Closed Stalk Containment -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ClosedStalkContainment

noncomputable section

/-! Containment of ideal sheaves is detected by local spectra, and by
closed-point local spectra when the source is quasi-compact. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]

theorem ideal_le_of_localSpectra (I J : X.IdealSheafData)
    (h : ∀ x : X, I.comap (X.fromSpecStalk x) ≤ J.comap (X.fromSpecStalk x)) : I ≤ J := by
  let : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have hj : J.comap J.subschemeι = ⊥ := by
    rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.map_bot, J.ker_subschemeι]
  have hz : I.comap J.subschemeι = ⊥ := by
    apply ClosedStalkDetection.ideal_eq_bot_of_localSpectra
    intro z
    have hc := Scheme.IdealSheafData.comap_mono (Spec.map (J.subschemeι.stalkMap z))
      (h (J.subschemeι z))
    dsimp only at hc
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp, hj, Scheme.IdealSheafData.comap_bot] at hc
    exact bot_unique hc
  have hi : I ≤ J.subschemeι.ker := by
    rw [← Scheme.IdealSheafData.map_bot J.subschemeι,
      Scheme.IdealSheafData.le_map_iff_comap_le, hz]
  exact hi.trans_eq J.ker_subschemeι

theorem ideal_le_of_closed_localSpectra [CompactSpace X] (I J : X.IdealSheafData)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      I.comap (X.fromSpecStalk x) ≤ J.comap (X.fromSpecStalk x)) : I ≤ J := by
  apply ideal_le_of_localSpectra I J
  intro x
  obtain ⟨y, hy, hyc⟩ := isClosed_closure.exists_closed_singleton
    (Set.singleton_nonempty x).closure
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hc := Scheme.IdealSheafData.comap_mono (Spec.map (X.presheaf.stalkSpecializes hxy)) (h y hyc)
  dsimp only at hc
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk] at hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ClosedStalkContainment
