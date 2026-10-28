import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.InjectiveCokernelSequence

/-! # Restriction Cohomology Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCohomologyBoundary.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

theorem openRestrictionPushforwardUnit_HSucc_eq_zero_of_cokernel_killed
    {X : Scheme.{u}} {F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X} {n : ℕ}
    (c : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH F (n + 1))
    (q : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH (cokernel (Injective.ι F)) n)
    (hq : q.comp (InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (U : X.Opens)
    (hqU : q.comp (Abelian.Ext.mk₀
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app
        (cokernel (Injective.ι F)))) rfl = 0)
    [IsIso (cokernelComparison (Injective.ι F)
      (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U))] :
    (c.comp (Abelian.Ext.mk₀
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F)) rfl :
        AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F) (n + 1)) = 0 := by
  let E := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U
  let η := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U
  let i := Injective.ι F
  let ζ := InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.openInjectiveCokernelMap U F
  let μ := cokernelComparison i E
  have hT := InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.openInjectiveCokernelSequence_shortExact U F
  change (ShortComplex.mk (E.map i) (cokernel.π (E.map i)) _).ShortExact at hT
  have hζμ : ζ ≫ μ = η.app (cokernel i) := by
    exact InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.openInjectiveCokernelMap_comp_cokernelComparison U F
  have hqζμ :
      (q.comp (Abelian.Ext.mk₀ ζ) rfl).comp
          (Abelian.Ext.mk₀ μ) rfl = 0 := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, hζμ]
    exact hqU
  have hqζ : q.comp (Abelian.Ext.mk₀ ζ) rfl = 0 := by
    apply InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.ext_postcomp_mk₀_injective_of_isIso
      ((CategoryTheory.constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))) μ n
    change
      (q.comp (Abelian.Ext.mk₀ ζ) rfl).comp
          (Abelian.Ext.mk₀ μ) rfl =
        (0 : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH (cokernel (E.map i)) n).comp
          (Abelian.Ext.mk₀ μ) rfl
    simpa using hqζμ
  calc
    c.comp (Abelian.Ext.mk₀ (η.app F)) rfl =
        (q.comp (InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass rfl).comp
          (Abelian.Ext.mk₀ (η.app F)) rfl := by rw [hq]
    _ = q.comp
        ((InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass.comp
          (Abelian.Ext.mk₀ (η.app F)) rfl) rfl := by
      rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
    _ = q.comp ((Abelian.Ext.mk₀ ζ).comp hT.extClass rfl) rfl := by
      exact congrArg (fun x ↦ q.comp x rfl)
        ((InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass_naturality
          hT (InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequenceToOpen U F))
    _ = (q.comp (Abelian.Ext.mk₀ ζ) rfl).comp hT.extClass rfl := by
      simpa only using (Abelian.Ext.comp_assoc q
        (Abelian.Ext.mk₀ ζ) hT.extClass rfl rfl rfl).symm
    _ = 0 := by rw [hqζ]; simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCohomologyBoundary.ZariskiCohomology.LocalKilling
