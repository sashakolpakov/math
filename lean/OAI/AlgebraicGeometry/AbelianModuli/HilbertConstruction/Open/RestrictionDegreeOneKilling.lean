import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCohomologyBoundary

/-! # Restriction Degree One Killing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionDegreeOneKilling.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

theorem openRestrictionPushforwardUnit_HOne_eq_zero_of_lift
    {X : Scheme.{u}} {F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X}
    (c : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH F 1)
    (q : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (U : X.Opens)
    (t : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj (Injective.under F)) 0)
    (ht : t.comp
        (Abelian.Ext.mk₀ ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map
          (cokernel.π (Injective.ι F)))) rfl =
      q.comp (Abelian.Ext.mk₀
        ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app
          (cokernel (Injective.ι F)))) rfl) :
    (c.comp (Abelian.Ext.mk₀
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F)) rfl :
        AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F) 1) =
      (0 : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F) 1) := by
  let E := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U
  let η := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U
  let i := Injective.ι F
  let π := cokernel.π i
  let ζ := InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.openInjectiveCokernelMap U F
  let μ := cokernelComparison i E
  have hT := InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.openInjectiveCokernelSequence_shortExact U F
  change (ShortComplex.mk (E.map i) (cokernel.π (E.map i)) _).ShortExact at hT
  let : Mono μ := by
    dsimp [μ, E, i]
    exact RestrictionCokernelComparison.ZariskiCohomology.LocalKilling.openRestrictionPushforward_cokernelComparison_mono U (Injective.ι F)
  have hζμ : ζ ≫ μ = η.app (cokernel i) :=
    InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.openInjectiveCokernelMap_comp_cokernelComparison U F
  have hπμ : cokernel.π (E.map i) ≫ μ = E.map π := by
    exact π_comp_cokernelComparison i E
  have hqζ : q.comp (Abelian.Ext.mk₀ ζ) rfl =
      t.comp (Abelian.Ext.mk₀ (cokernel.π (E.map i))) rfl := by
    refine (Abelian.Ext.postcomp_mk₀_injective_of_mono
      ((CategoryTheory.constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))) μ) ?_
    change
      (q.comp (Abelian.Ext.mk₀ ζ) rfl).comp
          (Abelian.Ext.mk₀ μ) rfl =
        (t.comp (Abelian.Ext.mk₀ (cokernel.π (E.map i))) rfl).comp
          (Abelian.Ext.mk₀ μ) rfl
    simpa only [Abelian.Ext.comp_assoc_of_third_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, hζμ, hπμ] using ht.symm
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
    _ = (t.comp (Abelian.Ext.mk₀ (cokernel.π (E.map i))) rfl).comp
        hT.extClass rfl := by rw [hqζ]
    _ = t.comp ((Abelian.Ext.mk₀ (cokernel.π (E.map i))).comp
        hT.extClass rfl) rfl := by
      simpa only using (Abelian.Ext.comp_assoc t
        (Abelian.Ext.mk₀ (cokernel.π (E.map i)))
          hT.extClass rfl rfl rfl)
    _ = 0 := by simp only [hT.comp_extClass, Abelian.Ext.comp_zero]

theorem openRestrictionPushforwardUnit_HOne_eq_zero_of_section_lift
    {X : Scheme.{u}} {F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X}
    (c : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH F 1)
    (q : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (U : X.Opens)
    (t : (Injective.under F).1.obj (op U))
    (ht : (cokernel.π (Injective.ι F)).hom.app (op U) t =
      (cokernel (Injective.ι F)).1.map (homOfLE le_top).op
        (CategoryTheory.Sheaf.H.equiv₀ (cokernel (Injective.ι F))
          (isTerminalTop : IsTerminal (⊤ : Opens X)) q)) :
    (c.comp (Abelian.Ext.mk₀
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F)) rfl :
        AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F) 1) = 0 := by
  apply openRestrictionPushforwardUnit_HOne_eq_zero_of_lift c q hq U
    (RestrictionCohomologyZero.ZariskiCohomology.LocalKilling.openRestrictionPushforwardHZeroOfSection U (Injective.under F) t)
  rw [RestrictionCohomologyZero.ZariskiCohomology.LocalKilling.openRestrictionPushforwardHZeroOfSection_map,
    RestrictionCohomologyZero.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit_HZero]
  exact congrArg
    (RestrictionCohomologyZero.ZariskiCohomology.LocalKilling.openRestrictionPushforwardHZeroOfSection U (cokernel (Injective.ι F))) ht

theorem exists_injectiveCokernel_class
    {X : Scheme.{u}} {F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X} {n : ℕ} (c : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH F (n + 1)) :
    ∃ q : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH (cokernel (Injective.ι F)) n,
      q.comp (InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass rfl = c := by
  let Z := (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))
  have hc : c.comp (Abelian.Ext.mk₀ (Injective.ι F)) rfl = 0 :=
    Abelian.Ext.eq_zero_of_injective _
  exact Abelian.Ext.covariant_sequence_exact₁ Z
    (InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F) c hc rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionDegreeOneKilling.ZariskiCohomology.LocalKilling
