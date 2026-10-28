import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionDegreeOneKilling

/-! # Local Cohomology Killing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LocalCohomologyKilling.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

theorem exists_affineOpen_HOne_killing
    {X : Scheme.{u}} {F : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X}
    (c : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH F 1)
    (q : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      (c.comp (Abelian.Ext.mk₀
        ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F)) rfl :
          Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F) 1) = 0 := by
  let π := cokernel.π (Injective.ι F)
  have hπepi : Epi π := by
    dsimp [π]
    infer_instance
  let s := CategoryTheory.Sheaf.H.equiv₀ (cokernel (Injective.ι F))
    (isTerminalTop : IsTerminal (⊤ : Opens X)) q
  have hlocal : TopCat.Presheaf.IsLocallySurjective π.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi π).2 hπepi
  have hex := (TopCat.Presheaf.isLocallySurjective_iff π.hom).1 hlocal
    (⊤ : Opens X) s x (by simp)
  rcases hex with ⟨V, hVtop, hpre, hxV⟩
  rcases hpre with ⟨t, ht⟩
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ V := hUV
  let tU := (Injective.under F).1.map (homOfLE hUV').op t
  have htU : π.hom.app (op U) tU =
      (cokernel (Injective.ι F)).1.map (homOfLE le_top).op s := by
    have ht' := congrArg
      (fun y ↦ (cokernel (Injective.ι F)).1.map (homOfLE hUV').op y) ht
    dsimp [tU]
    rw [← ConcreteCategory.comp_apply, ← π.hom.naturality] at ht'
    have hk : (homOfLE hVtop).op ≫ (homOfLE hUV').op =
        (homOfLE le_top).op := Subsingleton.elim _ _
    simpa only [TopCat.Presheaf.restrict, ← ConcreteCategory.comp_apply,
      ← (cokernel (Injective.ι F)).1.map_comp, hk] using ht'
  refine ⟨U, hU, hxU, ?_⟩
  exact Open.RestrictionDegreeOneKilling.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit_HOne_eq_zero_of_section_lift
    c q hq U tU htU

theorem exists_affineOpen_HTwo_killing_of_affine_cokernel_app_surjective
    {R : CommRingCat.{u}} {F : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf (Spec R)}
    (c : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH F 2)
    (q : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH (cokernel (Injective.ι F)) 1)
    (hq : q.comp (Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (hsurjective : ∀ (W : (Spec R).Opens), IsAffineOpen W →
      Function.Surjective
        ((cokernel.π (Injective.ι F)).hom.app (op W)))
    (x : Spec R) :
    ∃ U : (Spec R).Opens, IsAffineOpen U ∧ x ∈ U ∧
      (c.comp (Abelian.Ext.mk₀
        ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F)) rfl :
          Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F) 2) = 0 := by
  obtain ⟨r, hr⟩ := Open.RestrictionDegreeOneKilling.ZariskiCohomology.LocalKilling.exists_injectiveCokernel_class q
  obtain ⟨U, hU, hxU, hqU⟩ :=
    exists_affineOpen_HOne_killing q r hr x
  let : IsIso (cokernelComparison (Injective.ι F)
      (Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U)) :=
    Open.RestrictionCokernelComparison.ZariskiCohomology.LocalKilling.openRestrictionPushforward_cokernelComparison_isIso_of_affine_app_surjective
      U hU (Injective.ι F) hsurjective
  exact ⟨U, hU, hxU,
    Open.RestrictionCohomologyBoundary.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit_HSucc_eq_zero_of_cokernel_killed
      c q hq U hqU⟩

theorem exists_affineOpen_H_succ_killing_of_affine_syzygy_app_surjective
    {R : CommRingCat.{u}} {F : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf (Spec R)} (n : ℕ)
    (c : Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH F (n + 1))
    (hsurjective : Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.AffineSyzygyAppSurjective F n)
    (x : Spec R) :
    ∃ U : (Spec R).Opens, IsAffineOpen U ∧ x ∈ U ∧
      (c.comp (Abelian.Ext.mk₀
        ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F)) rfl :
          Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.ExtH ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).obj F) (n + 1)) = 0 := by
  induction n generalizing F with
  | zero =>
      obtain ⟨q, hq⟩ := Open.RestrictionDegreeOneKilling.ZariskiCohomology.LocalKilling.exists_injectiveCokernel_class (F := F) c
      exact exists_affineOpen_HOne_killing c q hq x
  | succ n ih =>
      cases hsurjective with
      | succ hfirst htail =>
          obtain ⟨q, hq⟩ := Open.RestrictionDegreeOneKilling.ZariskiCohomology.LocalKilling.exists_injectiveCokernel_class (F := F) c
          obtain ⟨U, hU, hxU, hqU⟩ := ih q htail
          let : IsIso (cokernelComparison (Injective.ι F)
              (Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U)) :=
            Open.RestrictionCokernelComparison.ZariskiCohomology.LocalKilling.openRestrictionPushforward_cokernelComparison_isIso_of_affine_app_surjective
              U hU (Injective.ι F) hfirst
          exact ⟨U, hU, hxU,
            Open.RestrictionCohomologyBoundary.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit_HSucc_eq_zero_of_cokernel_killed
              c q hq U hqU⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LocalCohomologyKilling.ZariskiCohomology.LocalKilling
