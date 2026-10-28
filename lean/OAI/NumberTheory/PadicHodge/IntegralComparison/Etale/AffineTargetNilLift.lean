import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineSchemeNilLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentOpenRestriction
import Mathlib.AlgebraicGeometry.Gluing

/-! # Affine Target Nil Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineTargetNilLift

noncomputable section

/-! The unique nilpotent lifting property of an actual affine etale
target holds for arbitrary source schemes, by gluing actual affine
lifts and using unramified uniqueness on their overlaps. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X Y T T₀ : Scheme.{u}} [IsAffine X] [IsAffine Y]
  (f : Y ⟶ X) [Etale f] (i : T₀ ⟶ T) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (a : T₀ ⟶ Y) (b : T ⟶ X) (hab : a ≫ f = i ≫ b)

include hi hab in
private theorem chart_exists (U : T.affineOpens) :
    ∃ l : U.1.toScheme ⟶ Y,
      (i ∣_ U.1) ≫ l = (i ⁻¹ᵁ U.1).ι ≫ a ∧ l ≫ f = U.1.ι ≫ b := by
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine (i ⁻¹ᵁ U.1).toScheme := U.2.preimage i
  exact (AffineSchemeNilLift.existsUnique_lift f (i ∣_ U.1)
    (NilpotentOpenRestriction.nilpotent i hi U.1) ((i ⁻¹ᵁ U.1).ι ≫ a)
    (U.1.ι ≫ b) (by rw [Category.assoc, hab, ← Category.assoc, ← morphismRestrict_ι]; simp only [Category.assoc])).exists

def chart (U : T.affineOpens) : U.1.toScheme ⟶ Y :=
  (chart_exists f i hi a b hab U).choose

theorem chart_reduction (U : T.affineOpens) :
    (i ∣_ U.1) ≫ chart f i hi a b hab U = (i ⁻¹ᵁ U.1).ι ≫ a :=
  (chart_exists f i hi a b hab U).choose_spec.1

theorem chart_base (U : T.affineOpens) :
    chart f i hi a b hab U ≫ f = U.1.ι ≫ b :=
  (chart_exists f i hi a b hab U).choose_spec.2

private theorem reduced_chart (U : T.affineOpens) {Z Z₀ : Scheme.{u}}
    (j : Z₀ ⟶ Z) (u : Z ⟶ U.1.toScheme) (v : Z₀ ⟶ T₀)
    (h : (j ≫ u) ≫ U.1.ι = v ≫ i) :
    j ≫ u ≫ chart f i hi a b hab U = v ≫ a := by
  let hp := isPullback_morphismRestrict i U.1
  let l := hp.lift (j ≫ u) v h
  calc
    _ = l ≫ (i ∣_ U.1) ≫ chart f i hi a b hab U := by
      simpa only [Category.assoc] using
        (congrArg (fun w => w ≫ chart f i hi a b hab U) (hp.lift_fst (j ≫ u) v h)).symm
    _ = l ≫ (i ⁻¹ᵁ U.1).ι ≫ a := by rw [chart_reduction]
    _ = _ := by rw [← Category.assoc, hp.lift_snd]

def cover : T.OpenCover := T.openCoverOfIsOpenCover (fun U : T.affineOpens => U.1) (iSup_affineOpens_eq_top T)

theorem chart_compatible (U V : T.affineOpens) :
    pullback.fst U.1.ι V.1.ι ≫ chart f i hi a b hab U =
      pullback.snd U.1.ι V.1.ι ≫ chart f i hi a b hab V := by
  let k := pullback.fst U.1.ι V.1.ι ≫ U.1.ι
  let j := pullback.snd i k
  let v := pullback.fst i k
  have hp : IsPullback j v k i := (IsPullback.of_hasPullback i k).flip
  have hj : IsNilpotent j.ker := NilpotentOpenRestriction.nilpotent_of_isPullback i hi j v k hp
  apply FormallyUnramified.hom_ext j hj f
  · have hU : (j ≫ pullback.fst U.1.ι V.1.ι) ≫ U.1.ι = v ≫ i := by
      simpa only [Category.assoc] using hp.w
    have hV : (j ≫ pullback.snd U.1.ι V.1.ι) ≫ V.1.ι = v ≫ i := by
      rw [Category.assoc, ← pullback.condition]
      exact hp.w
    exact (reduced_chart f i hi a b hab U j _ v hU).trans
      (reduced_chart f i hi a b hab V j _ v hV).symm
  · rw [Category.assoc, Category.assoc, chart_base, chart_base,
      ← Category.assoc, ← Category.assoc, pullback.condition]

def lift : T ⟶ Y := (cover (T := T)).glueMorphisms
  (chart f i hi a b hab) (chart_compatible f i hi a b hab)

theorem lift_chart (U : T.affineOpens) : U.1.ι ≫ AffineTargetNilLift.lift f i hi a b hab = chart f i hi a b hab U :=
  (cover (T := T)).ι_glueMorphisms _ _ U

private def reducedCover : T₀.OpenCover where
  I₀ := T.affineOpens
  X U := (i ⁻¹ᵁ U.1).toScheme
  f U := (i ⁻¹ᵁ U.1).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have hx : i x ∈ ⨆ U : T.affineOpens, U.1 := (iSup_affineOpens_eq_top T).symm ▸ trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U, ⟨⟨x, hU⟩, rfl⟩⟩

theorem lift_reduction : i ≫ AffineTargetNilLift.lift f i hi a b hab = a := by
  apply (reducedCover i).hom_ext
  intro U
  change (i ⁻¹ᵁ U.1).ι ≫ (i ≫ AffineTargetNilLift.lift f i hi a b hab) = (i ⁻¹ᵁ U.1).ι ≫ a
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc, lift_chart, chart_reduction]

theorem lift_base : AffineTargetNilLift.lift f i hi a b hab ≫ f = b := by
  apply (cover (T := T)).hom_ext
  intro U
  change U.1.ι ≫ (AffineTargetNilLift.lift f i hi a b hab ≫ f) = U.1.ι ≫ b
  rw [← Category.assoc, lift_chart, chart_base]

include hi hab in
theorem existsUnique_lift : ∃! l : T ⟶ Y, i ≫ l = a ∧ l ≫ f = b := by
  refine ⟨AffineTargetNilLift.lift f i hi a b hab, ⟨lift_reduction f i hi a b hab, lift_base f i hi a b hab⟩, ?_⟩
  intro l hl
  exact FormallyUnramified.hom_ext i hi f
    (hl.1.trans (lift_reduction f i hi a b hab).symm)
    (hl.2.trans (lift_base f i hi a b hab).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineTargetNilLift
