import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechFrame

/-! # Frame Iso Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.FrameIsoRecovery

noncomputable section

/-! Equality of the original regular transition units glues the given
native frames to an actual isomorphism of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_iso_of_localFrame_transitions {X : Scheme.{0}} {I : Type}
    {M N : X.Modules} (s : I → LineFrameAtlas.LocalLineFrame M) (t : I → LineFrameAtlas.LocalLineFrame N)
    (hU : IsOpenCover (fun i => (s i).domain)) (ht : ∀ i, (t i).domain = (s i).domain)
    (h : ∀ i j, (s i).transition (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right =
      (t i).transition (t j) ((s i).domain ⊓ (s j).domain)
        (inf_le_left.trans (ht i).ge) (inf_le_right.trans (ht j).ge)) : Nonempty (M ≅ N) := by
  let U := fun i => (s i).domain
  let e := fun i => SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M (U i) (s i).frame
  let g := fun i => SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N (t i).domain
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N (t i).domain (t i).frame)
      (Over.mk (homOfLE (ht i).ge))
  let a : ∀ i j, Γ(X, U i ⊓ U j) := fun i j => ((s i).transition (s j) _ inf_le_left inf_le_right).val
  obtain ⟨f, _⟩ := RepresentationTheory.Theta.Geometric.FramedUnitGluing.exists_iso_of_framed_units M N U hU.iSup_eq_top e g (fun _ => 1) a a
    (fun i j => LineFrameAtlas.LocalLineFrame.overFrame_transition (s i) (s j) _ inf_le_left inf_le_right)
    (fun i j => by
      dsimp only [g]
      rw [SheafCohomology.Projective.OpenFrameTransitivity.restrictOverTrivialization_comp, SheafCohomology.Projective.OpenFrameTransitivity.restrictOverTrivialization_comp]
      exact (LineFrameAtlas.LocalLineFrame.overFrame_transition (t i) (t j) _ _ _).trans
        (congrArg (fun b : Γ(X, U i ⊓ U j)ˣ => _ ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf _ b.val)
          (h i j).symm))
    (fun _ _ => by simp only [RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit, map_one, Units.val_one, mul_one, one_mul])
  exact ⟨f⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.FrameIsoRecovery
