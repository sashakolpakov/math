import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FaithfulLinePullback
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModulePullbackOpen

/-! # Faithful Pullback Unit -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FaithfulPullbackUnit

noncomputable section

/-! Faithfully flat pullback units for actual line bundles are monomorphisms.
This gives uniqueness for local factorizations through the unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModulePullbackOpen.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FunctionDescent OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenHomComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FaithfulLinePullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]

theorem app_injective (U : Y.Opens) : Function.Injective (f.app U) := by
  let g := f ∣_ U
  have : Flat g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f U).flip (inferInstanceAs (Flat f))
  have : Surjective g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  have : Epi g := Flat.epi_of_flat_of_surjective g
  have hi : Function.Injective (f.app (U.ι ''ᵁ ⊤)) := by
    intro r s hrs
    apply FunctionDescent.appTop_injective_of_epi g
    change (f ∣_ U).appTop r = (f ∣_ U).appTop s
    rw [morphismRestrict_appTop]
    change X.presheaf.map _ (f.app _ r) = X.presheaf.map _ (f.app _ s)
    rw [hrs]
  exact (congrArg (fun V : Y.Opens ↦ Function.Injective (f.app V)) U.ι_image_top).mp hi

theorem structureSheafToPushforward_mono : Mono (ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward f) where
  right_cancellation a b hab := by
    apply Scheme.Modules.hom_ext
    intro U
    ext m
    apply app_injective f U
    exact congrArg (fun q ↦ q.app U m) hab

theorem unit_structureSheaf_mono :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)) := by
  have := structureSheafToPushforward_mono f
  have h : Mono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) ≫
      (Scheme.Modules.pushforward f).map (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f).hom) := by
    rw [ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.pullbackStructureSheafIso_unit]
    infer_instance
  exact mono_of_mono_fac (show
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) ≫
      (Scheme.Modules.pushforward f).map (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) ≫
      (Scheme.Modules.pushforward f).map (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f).hom from rfl)

theorem unit_trivial_mono {M : Y.Modules} (e : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have : Mono (adj.unit.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)) := unit_structureSheaf_mono f
  exact mono_of_mono_fac (adj.unit.naturality e.hom).symm

omit [Flat f] [Surjective f] in
theorem mono_of_locally_restrict_mono {M N : Y.Modules} (a : M ⟶ N)
    {ι : Type*} (U : ι → Y.Opens) (hU : (⊤ : Y.Opens) ≤ iSup U)
    (ha : ∀ i, Mono ((Scheme.Modules.restrictFunctor (U i).ι).map a)) : Mono a where
  right_cancellation b c hbc := by
    apply OpenHomComparison.hom_eq_of_open_pullbacks _ _ U hU b c
    intro i
    apply FaithfulLinePullback.map_eq_through_natIso (Scheme.Modules.restrictFunctorIsoPullback (U i).ι)
    have := ha i
    apply (cancel_mono ((Scheme.Modules.restrictFunctor (U i).ι).map a)).mp
    rw [← (Scheme.Modules.restrictFunctor (U i).ι).map_comp,
      ← (Scheme.Modules.restrictFunctor (U i).ι).map_comp, hbc]

/-- The actual adjunction unit is monic for every line bundle, without
reducedness or a global trivialization. -/
theorem unit_line_mono {M : Y.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  choose U hyU he using hM
  have hU : (⊤ : Y.Opens) ≤ iSup U := by
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  apply mono_of_locally_restrict_mono _ U hU
  intro y
  let g := f ∣_ U y
  have : Flat g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f (U y)).flip (inferInstanceAs (Flat f))
  have : Surjective g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f (U y)).flip (inferInstanceAs (Surjective f))
  let e : M.restrict (U y).ι ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (U y).toScheme :=
    (Scheme.Modules.restrictFunctorIsoPullback (U y).ι).app M ≪≫ Classical.choice (he y)
  have : Mono ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (M.restrict (U y).ι)) :=
    unit_trivial_mono g e
  exact mono_of_mono_fac (ArithmeticGeometry.OrdinaryLocus.Openness.ModulePullbackOpen.Construction.modulePullbackOpen_unit f (U y) M)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FaithfulPullbackUnit
