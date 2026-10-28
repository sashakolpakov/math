import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformAtlasOpenGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.LengthHead
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.StopPrefixComparisonTrace

/-! # Trace Open Cover Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A prescribed incidence trace descends through an actual open family of whole-prefix comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.hasIncidenceTrace_of_open_comparisons
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ [Nonempty X] (ι : Type) (U : ι → Scheme) (j : ∀ i, U i ⟶ X)
      [∀ i, IsIntegral (U i)] [∀ i, IsLocallyNoetherian (U i)] [∀ i, IsOpenImmersion (j i)],
      (∀ x : X, ∃ i y, j i y = x) →
      ∀ (h : ∀ i, U i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : ∀ i, (U i).IdealSheafData)
        (V : ι → Scheme) (k : ∀ i, V i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : ∀ i, (V i).IdealSheafData)
        (Q : ∀ i, Smooth.ControlPrefix.Construction.SmoothControlPrefix b (U i) (h i) (L i) (V i) (k i) (M i))
        (r : ∀ i, V i ⟶ Y),
        (∀ i, P.EtaleComparison (Q i) (j i) (r i)) →
        ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β),
          (∀ i, (Q i).HasIncidenceTrace β (fun l => (D l).comap (j i)) T) →
          P.HasIncidenceTrace β D T := by
  classical
  induction P with
  | @stop X f hf J =>
      intro _ ι U j _ _ _ hcover h L V k M Q r hc β _ D T hT
      cases T with
      | stop =>
          let C : X.OpenCover := Scheme.Cover.mkOfCovers ι U j hcover
          apply Global.UniformAtlasOpenGluing.Construction.exists_boundary_atlas_of_openCover f D C
          intro i
          change ι at i
          exact Smooth.ControlPrefix.Construction.SmoothControlPrefix.trace_on_source_of_comparison_from_stop (Q i) (j i) (r i) (hc i) β D (.stop β) (hT i)
      | step F T =>
          obtain ⟨i, _, _⟩ := hcover (Classical.choice (inferInstance : Nonempty X))
          exact False.elim (Smooth.ControlPrefix.Construction.SmoothControlPrefix.trace_on_source_of_comparison_from_stop (Q i) (j i) (r i) (hc i)
            β D (.step F T) (hT i))
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro _ ι U j _ _ _ hcover h L V k M Q r hc β _ D T hT
      have hheads := fun i => Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_blowup_of_stepCount_succ (Q i) tail.stepCount
        ((hc i).stepCount_eq (Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hb hp hs hbl tail) (Q i) (j i) (r i)).symm
      choose C hC hbC hpC hsC hblC rest hQ hcount using hheads
      have hd : ∀ i, Etale (j i) ∧ j i ≫ f = h i ∧ J.comap (j i) = L i ∧
          ∃ he : I.comap (j i) = C i,
            tail.EtaleComparison (rest i) (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo (j i) I (C i) he hI (hC i)) (r i) := by
        intro i
        have hi := hc i
        rw [hQ i] at hi
        exact (Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hb hp hs hbl tail
          (C i) (hC i) (hbC i) (hpC i) (hsC i) (hblC i) (rest i) (j i) (r i)).mp hi
      choose het hf hJ he hcomp using hd
      cases T with
      | stop =>
          obtain ⟨i, _, _⟩ := hcover (Classical.choice (inferInstance : Nonempty X))
          have ht := hT i
          rw [hQ i] at ht
          exact False.elim ht
      | step F T =>
          have hlocal : ∀ i, (∃ A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (h i) (C i)
              (fun l => (D l).comap (j i)), ∀ a, A.divided a = F) ∧
              (rest i).HasIncidenceTrace (Option β)
                (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (C i) (hC i) (fun l => (D l).comap (j i))) T := by
            intro i
            have ht := hT i
            rw [hQ i] at ht
            exact ht
          let O : X.OpenCover := Scheme.Cover.mkOfCovers ι U j hcover
          have hA : ∃ A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D, ∀ a, A.divided a = F := by
            apply Global.UniformAtlasOpenGluing.Construction.exists_uniform_mixed_atlas_of_openCover f I D F O
            intro i
            change ι at i
            change ∃ A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (j i ≫ f) (I.comap (j i))
              (fun l => (D l).comap (j i)), ∀ a, A.divided a = F
            rw [hf i, he i]
            exact (hlocal i).1
          let U' := fun i => GlobalBlowup.Data.Construction.globalBlowup (C i) (hC i)
          let j' := fun i => GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo (j i) I (C i) (he i) hI (hC i)
          let h' := fun i => GlobalBlowup.Data.Construction.globalBlowupToBase (C i) (hC i) ≫ h i
          let L' := fun i => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (C i) (L i) (hC i) b
          let : ∀ i, IsIntegral (U' i) := fun i => inferInstanceAs (IsIntegral (GlobalBlowup.Data.Construction.globalBlowup (C i) (hC i)))
          let : ∀ i, IsLocallyNoetherian (U' i) := fun i => inferInstanceAs (IsLocallyNoetherian (GlobalBlowup.Data.Construction.globalBlowup (C i) (hC i)))
          let : ∀ i, IsOpenImmersion (j' i) := fun i =>
            GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_isOpenImmersion (j i) I (C i) (he i) hI (hC i)
          have hcover' : ∀ x : GlobalBlowup.Data.Construction.globalBlowup I hI, ∃ i y, j' i y = x := by
            intro x
            obtain ⟨i, y, hy⟩ := hcover (GlobalBlowup.Data.Construction.globalBlowupToBase I hI x)
            obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
              (GlobalBlowup.EtalePullback.Construction.globalBlowupMapTo_etale_isPullback (j i) I (C i) (he i) hI (hC i)) x y hy.symm
            exact ⟨i, z, hz⟩
          have ht' : ∀ i, (rest i).HasIncidenceTrace (Option β)
              (fun l => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l).comap (j' i)) T := by
            intro i
            have hboundary : (fun l => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l).comap (j' i)) =
                CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (C i) (hC i) (fun l => (D l).comap (j i)) := by
              funext l
              exact GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_canonicalBoundary_etale (j i) I (C i) (he i) hI (hC i) D l
            rw [hboundary]
            exact (hlocal i).2
          exact ⟨hA, ih ι U' j' hcover' h' L' V k M rest r hcomp
            (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) T ht'⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
