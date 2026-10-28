import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.FaithfulPullbackUnit
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Dominant Line Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.DominantLinePullback.IntrinsicDominantPullback

noncomputable section

/-! Faithfulness for line bundles only needs an injective structure
sheaf map. It applies to the nonflat square-zero parameter injection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.FaithfulLinePullback.PicardFaithfulLinePullback OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares

theorem framedPullback_injective_of_appTop {X Y : Scheme} (f : X ⟶ Y)
    (hf : Function.Injective f.appTop) {M N : Y.Modules}
    (eM : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) (eN : N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) :
    Function.Injective (fun a : M ⟶ N => (Scheme.Modules.pullback f).map a) := by
  intro a b hab
  apply (OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedHomEquiv eM eN).symm.injective
  change OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedCoefficient eM eN a = OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedCoefficient eM eN b
  apply hf
  rw [← OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedCoefficient_pullback, ← OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedCoefficient_pullback]
  exact congrArg (OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedCoefficient (OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame f eM) (OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame f eN)) hab

variable {X Y : Scheme} (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]

theorem linePullback_injective {M N : Y.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N) :
    Function.Injective (fun a : M ⟶ N => (Scheme.Modules.pullback f).map a) := by
  intro a b hab
  choose U hxU heM using hM
  choose V hxV heN using hN
  let W (y : Y) := U y ⊓ V y
  have hW : (⊤ : Y.Opens) ≤ iSup W := by
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y, hxV y⟩
  apply OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenHomComparison.PicardOpenHomComparison.hom_eq_of_open_pullbacks M N W hW a b
  intro y
  let eM := ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction.restrictLineBundleTrivialization (show W y ≤ U y from inf_le_left) (Classical.choice (heM y))
  let eN := ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction.restrictLineBundleTrivialization (show W y ≤ V y from inf_le_right) (Classical.choice (heN y))
  let g := f ∣_ W y
  have : IsSchemeTheoreticallyDominant g :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict f (W y)).flip
  have : QuasiCompact g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f (W y)).flip (inferInstanceAs (QuasiCompact f))
  apply framedPullback_injective_of_appTop g (g.app_injective ⊤) eM eN
  let α := OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f (W y).ι (f ⁻¹ᵁ W y).ι g (morphismRestrict_ι f (W y)).symm
  exact OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.FaithfulLinePullback.PicardFaithfulLinePullback.map_eq_through_natIso α (congrArg (Scheme.Modules.pullback (f ⁻¹ᵁ W y).ι).map hab)

theorem structureSheafToPushforward_mono : Mono (ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward f) where
  right_cancellation a b hab := by
    apply Scheme.Modules.hom_ext
    intro U
    ext m
    apply f.app_injective U
    exact congrArg (fun q => q.app U m) hab

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

theorem unit_line_mono {M : Y.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  choose U hyU he using hM
  have hU : (⊤ : Y.Opens) ≤ iSup U := by
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  apply OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.FaithfulPullbackUnit.PicardFaithfulPullbackUnit.mono_of_locally_restrict_mono _ U hU
  intro y
  let g := f ∣_ U y
  have : IsSchemeTheoreticallyDominant g :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict f (U y)).flip
  have : QuasiCompact g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f (U y)).flip (inferInstanceAs (QuasiCompact f))
  let e : M.restrict (U y).ι ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (U y).toScheme :=
    (Scheme.Modules.restrictFunctorIsoPullback (U y).ι).app M ≪≫ Classical.choice (he y)
  have : Mono ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (M.restrict (U y).ι)) :=
    unit_trivial_mono g e
  exact mono_of_mono_fac (ArithmeticGeometry.OrdinaryLocus.Openness.ModulePullbackOpen.Construction.modulePullbackOpen_unit f (U y) M)

end

end OAI.RepresentationTheory.Theta.Geometric.DominantLinePullback.IntrinsicDominantPullback
