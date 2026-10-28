import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardPullback
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleFibers

/-! # Picard Field -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardField.Construction

noncomputable section

/-! Picard groups of field spectra and constant morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

instance picardFieldSubsingleton (k : Type u) [Field k] : Subsingleton (PicardEq.Construction.Picard (Spec (.of k))) where
  allEq a b := Quotient.inductionOn₂ a b fun L M ↦ Quotient.sound
    ⟨LineBundleFibers.Construction.lineBundleTrivializationOfSubsingleton L.sheaf L.isLineBundle ≪≫
      (LineBundleFibers.Construction.lineBundleTrivializationOfSubsingleton M.sheaf M.isLineBundle).symm⟩

theorem picardPullback_field_eq_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X) (a : PicardEq.Construction.Picard X) : PicardPullback.Construction.picardPullback x a = 0 := Subsingleton.elim _ _

theorem picardPullback_constant {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (a : PicardEq.Construction.Picard Y) :
    PicardPullback.Construction.picardPullback (f ≫ y) a = 0 := by
  rw [PicardPullback.Construction.picardPullback_comp]
  change PicardPullback.Construction.picardPullback f (PicardPullback.Construction.picardPullback y a) = 0
  rw [picardPullback_field_eq_zero, map_zero]

theorem picardPullback_injective_of_section {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) : Function.Injective (PicardPullback.Construction.picardPullback f) := by
  have h : Function.LeftInverse (PicardPullback.Construction.picardPullback s) (PicardPullback.Construction.picardPullback f) := by
    intro a
    have hc := congrArg (fun g : PicardEq.Construction.Picard Y →+ PicardEq.Construction.Picard Y ↦ g a) (PicardPullback.Construction.picardPullback_comp s f)
    rw [hs, PicardPullback.Construction.picardPullback_id] at hc
    exact hc.symm
  exact h.injective

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardField.Construction
