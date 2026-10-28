import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TorsionSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineTrivializationOf

/-! # From Power Sections -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FromPowerSections.Construction.FiniteFromPowerSections

noncomputable section

/-! A proper map is finite when suitable powers of line bundles defining
affine section neighborhoods are pulled back from its target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (h : ∀ x : X, ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (n : ℕ), 0 < n ∧
      Nonempty ((L.tensorPower n).sheaf ≅ (M.pullback f).sheaf) ∧
      ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf,
        x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ∧ IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)) : IsFinite f := by
  have : LocallyQuasiFinite f := (locallyQuasiFinite_iff_isFinite_fiber (f := f)).mpr (by
    intro y
    let i := f.fiberι y
    let p := f.fiberToSpecResidueField y
    let a := Y.fromSpecResidueField y
    let T : Over (Spec (Y.residueField y)) := Over.mk p
    have hpT : IsProper T.hom := inferInstanceAs (IsProper (pullback.snd f a))
    have ha : IsAffineHom a := @LineTrivializationOf.Construction.LineTrivialization.isAffineHom_from_field
      (Y.residueField y) inferInstance Y a
    have : IsAffineHom i :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f a).flip ha
    have hT : IsFinite T.hom := @TorsionSection.Construction.TorsionSectionFinite.isFinite
      (Y.residueField y) inferInstance T hpT (by
      intro x
      obtain ⟨L, M, n, hn, ⟨e⟩, s, hx, hs⟩ := h (i x)
      obtain ⟨e₀⟩ := @LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field
        (Y.residueField y) inferInstance Y a M
      let eT : ((L.pullback i).tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
        (TensorPullback.Construction.TensorPullbackMap.iso i L n).symm ≪≫
          (Scheme.Modules.pullback i).mapIso e ≪≫
          (Scheme.Modules.pullbackComp i f).app M.sheaf ≪≫
          (Scheme.Modules.pullbackCongr (f.fiber_fac y)).app M.sheaf ≪≫
          (Scheme.Modules.pullbackComp p a).symm.app M.sheaf ≪≫
          (Scheme.Modules.pullback p).mapIso e₀ ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p
      let t := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i s
      have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = i ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
        SectionBase.Construction.SectionBaseChange.nonvanishing_pullback i L s
      exact ⟨L.pullback i, n, hn, ⟨eT⟩, t, ht.symm ▸ hx, ht.symm ▸ hs.preimage i⟩)
    exact hT)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FromPowerSections.Construction.FiniteFromPowerSections
