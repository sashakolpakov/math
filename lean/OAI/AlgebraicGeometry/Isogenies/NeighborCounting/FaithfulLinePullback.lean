import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenHomComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedSquares

/-! # Faithful Line Pullback -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FaithfulLinePullback

noncomputable section

/-! Faithfulness of fpqc pullback on actual line-bundle morphisms,
proved locally using frames and regular-function descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenHomComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedSquares

theorem map_eq_through_natIso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} {a b : M ⟶ N} (h : F.map a = F.map b) :
    G.map a = G.map b := by
  apply (cancel_epi (e.hom.app M)).mp
  rw [← e.hom.naturality, ← e.hom.naturality, h]

theorem linePullback_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f] {M N : Y.Modules}
    (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N) :
    Function.Injective (fun a : M ⟶ N ↦ (Scheme.Modules.pullback f).map a) := by
  intro a b hab
  choose U hxU heM using hM
  choose V hxV heN using hN
  let W (y : Y) := U y ⊓ V y
  have hW : (⊤ : Y.Opens) ≤ iSup W := by
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y, hxV y⟩
  apply OpenHomComparison.hom_eq_of_open_pullbacks M N W hW a b
  intro y
  let eM := ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction.restrictLineBundleTrivialization (show W y ≤ U y from inf_le_left)
    (Classical.choice (heM y))
  let eN := ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction.Construction.restrictLineBundleTrivialization (show W y ≤ V y from inf_le_right)
    (Classical.choice (heN y))
  let g := f ∣_ W y
  have : Surjective g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f (W y)).flip (inferInstanceAs (Surjective f))
  have : Flat g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f (W y)).flip (inferInstanceAs (Flat f))
  have : QuasiCompact g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f (W y)).flip (inferInstanceAs (QuasiCompact f))
  apply FramedDescent.framedPullback_injective g eM eN
  let α := NormalizedSquares.sectionSquareIso f (W y).ι (f ⁻¹ᵁ W y).ι g (morphismRestrict_ι f (W y)).symm
  exact map_eq_through_natIso α
    (congrArg (Scheme.Modules.pullback (f ⁻¹ᵁ W y).ι).map hab)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FaithfulLinePullback
