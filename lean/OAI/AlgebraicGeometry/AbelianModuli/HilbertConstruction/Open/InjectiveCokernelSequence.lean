import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCokernelComparison

/-! # Injective Cokernel Sequence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

theorem ext_postcomp_mk₀_injective_of_isIso
    {X : Scheme.{u}} (L : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) {M N : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X}
    (f : M ⟶ N) [IsIso f] (n : ℕ) :
    Function.Injective
      ((Abelian.Ext.mk₀ f).postcomp L (add_zero n)) := by
  intro x y hxy
  have hxy' := congrArg
    (fun z ↦ z.comp (Abelian.Ext.mk₀ (inv f)) rfl) hxy
  change
    (x.comp (Abelian.Ext.mk₀ f) rfl).comp
        (Abelian.Ext.mk₀ (inv f)) rfl =
      (y.comp (Abelian.Ext.mk₀ f) rfl).comp
        (Abelian.Ext.mk₀ (inv f)) rfl at hxy'
  simpa only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, IsIso.hom_inv_id,
    Abelian.Ext.comp_mk₀_id] using hxy'

noncomputable abbrev injectiveCokernelSequence
    {X : Scheme.{u}} (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :
    ShortComplex (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

theorem injectiveCokernelSequence_shortExact
    {X : Scheme.{u}} (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :
    (injectiveCokernelSequence F).ShortExact := by
  let : Mono (injectiveCokernelSequence F).f := by
    change Mono (Injective.ι F)
    infer_instance
  let : Epi (injectiveCokernelSequence F).g := by
    change Epi (cokernel.π (Injective.ι F))
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.cokernelSequence_exact (Injective.ι F))

/-- The exact affine section-surjectivity data needed for a finite number of
injective-cokernel dimension shifts. -/
inductive AffineSyzygyAppSurjective {R : CommRingCat.{u}} :
    AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf (Spec R) → ℕ → Prop
  | zero (F) : AffineSyzygyAppSurjective F 0
  | succ {F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf (Spec R)} {n : ℕ}
      (head : ∀ (W : (Spec R).Opens), IsAffineOpen W →
        Function.Surjective
          ((cokernel.π (Injective.ι F)).hom.app (op W)))
      (tail : AffineSyzygyAppSurjective
        (cokernel (Injective.ι F)) n) :
      AffineSyzygyAppSurjective F (n + 1)

noncomputable abbrev openInjectiveCokernelSequence
    {X : Scheme.{u}} (U : X.Opens)
    (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :
    ShortComplex (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :=
  let E := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U
  ShortComplex.mk (E.map (Injective.ι F))
    (cokernel.π (E.map (Injective.ι F)))
    (cokernel.condition (E.map (Injective.ι F)))

theorem openInjectiveCokernelSequence_shortExact
    {X : Scheme.{u}} (U : X.Opens)
    (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :
    (openInjectiveCokernelSequence U F).ShortExact := by
  let : Mono ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map (Injective.ι F)) :=
    RestrictionCokernelComparison.ZariskiCohomology.LocalKilling.openRestrictionPushforward_map_mono U (Injective.ι F)
  let : Mono (openInjectiveCokernelSequence U F).f := by
    change Mono ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map (Injective.ι F))
    infer_instance
  let : Epi (openInjectiveCokernelSequence U F).g := by
    change Epi (cokernel.π
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map (Injective.ι F)))
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.cokernelSequence_exact
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map (Injective.ι F)))

noncomputable def openInjectiveCokernelMap
    {X : Scheme.{u}} (U : X.Opens)
    (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :
    cokernel (Injective.ι F) ⟶
      cokernel ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map (Injective.ι F)) :=
  cokernel.map (Injective.ι F)
    ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U).map (Injective.ι F))
    ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F)
    ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app (Injective.under F))
    ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).naturality (Injective.ι F))

noncomputable def injectiveCokernelSequenceToOpen
    {X : Scheme.{u}} (U : X.Opens)
    (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :
    injectiveCokernelSequence F ⟶ openInjectiveCokernelSequence U F where
  τ₁ := (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app F
  τ₂ := (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app (Injective.under F)
  τ₃ := openInjectiveCokernelMap U F
  comm₁₂ := by
    simpa [injectiveCokernelSequence, openInjectiveCokernelSequence] using
      ((AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).naturality (Injective.ι F)).symm
  comm₂₃ := by
    simp [injectiveCokernelSequence, openInjectiveCokernelSequence,
      openInjectiveCokernelMap]

theorem openInjectiveCokernelMap_comp_cokernelComparison
    {X : Scheme.{u}} (U : X.Opens) (F : AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X) :
    openInjectiveCokernelMap U F ≫
        cokernelComparison (Injective.ι F)
          (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U) =
      (AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U).app
        (cokernel (Injective.ι F)) := by
  let E := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforward U
  let η := AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openRestrictionPushforwardUnit U
  let i := Injective.ι F
  let π := cokernel.π i
  let ζ := openInjectiveCokernelMap U F
  let μ := cokernelComparison i E
  have hπζ : cokernel.π i ≫ ζ =
      η.app (Injective.under F) ≫ cokernel.π (E.map i) := by
    dsimp [ζ, η, E, i, openInjectiveCokernelMap]
    apply cokernel.π_desc
  rw [← cancel_epi (cokernel.π i)]
  calc
    cokernel.π i ≫ (ζ ≫ μ) =
        (cokernel.π i ≫ ζ) ≫ μ := Category.assoc _ _ _ |>.symm
    _ = (η.app (Injective.under F) ≫
        cokernel.π (E.map i)) ≫ μ := by rw [hπζ]
    _ = η.app (Injective.under F) ≫
        (cokernel.π (E.map i) ≫ μ) := Category.assoc _ _ _
    _ = η.app (Injective.under F) ≫ E.map π := by
      rw [π_comp_cokernelComparison]
    _ = cokernel.π i ≫ η.app (cokernel i) :=
      (η.naturality (cokernel.π i)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling
