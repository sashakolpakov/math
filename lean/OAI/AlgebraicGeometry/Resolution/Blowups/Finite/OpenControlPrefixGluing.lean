import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenBlowupCenterGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterOpenOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.CompatiblePrefixTail
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.LengthHead

/-! # Open Control Prefix Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Compatible finite open families of actual permissible programs glue, preserving all steps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_of_finite_open_compatible (b N : ℕ) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData)
      (ι : Type) [Finite ι] (U : ι → Scheme) (j : ∀ i, U i ⟶ X)
      [∀ i, IsIntegral (U i)] [∀ i, IsLocallyNoetherian (U i)]
      [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
      (_hcover : ∀ x : X, ∃ i y, j i y = x)
      (g : ∀ i, U i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : ∀ i, (U i).IdealSheafData)
      (_hg : ∀ i, j i ≫ f = g i) (_hL : ∀ i, J.comap (j i) = L i)
      (V : ι → Scheme) (k : ∀ i, V i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : ∀ i, (V i).IdealSheafData)
      (P : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (U i) (g i) (L i) (V i) (k i) (M i)),
      (∀ i, (P i).stepCount = N) → (∀ i a, (P i).OpenCompatible (P a) (j i) (j a)) →
      ∃ (Y : Scheme) (h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y h K) (r : ∀ i, V i ⟶ Y),
        ∀ i, Q.EtaleComparison (P i) (j i) (r i) := by
  classical
  induction N with
  | zero =>
      intro X _ _ f _ J ι _ U j _ _ _ _ hcover g L hg hL V k M P hN H
      have hr := fun i => Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_comparison_from_stop_of_stepCount_zero (P i) (j i) (hg i) (hL i) (hN i)
      choose r hr using hr
      exact ⟨X, f, J, .stop, r, hr⟩
  | succ N ih =>
      intro X _ _ f _ J ι _ U j _ _ _ _ hcover g L hg hL V k M P hN H
      have hheads := fun i => Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_blowup_of_stepCount_succ (P i) N (hN i)
      choose I hI hb hp hs hbl tail hP htail using hheads
      have hcompat : ∀ i a, (I i).comap (pullback.fst (j i) (j a)) =
          (I a).comap (pullback.snd (j i) (j a)) := by
        intro i a
        let : Smooth ((I i).subschemeι ≫ g i) := hs i
        let : Smooth ((I a).subschemeι ≫ g a) := hs a
        apply Blowups.Smooth.CenterOpenOverlap.Construction.smooth_center_open_overlap_eq (j i) (j a) (g i) (g a) (I i) (I a)
        have H' := H i a
        rw [hP i, hP a] at H'
        exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.OpenCompatible.head_support (I i) (hI i) (hb i) (hp i) (hs i) (hbl i) (tail i)
          (I a) (hI a) (hb a) (hp a) (hs a) (hbl a) (tail a) (j i) (j a) H'
      let C : X.OpenCover := Scheme.Cover.mkOfCovers ι U j hcover
      let : Finite C.I₀ := (inferInstance : Finite ι)
      let : ∀ i, IsIntegral (C.X i) := by change ∀ i : ι, IsIntegral (U i); infer_instance
      let : ∀ i, IsLocallyNoetherian (C.X i) := by change ∀ i : ι, IsLocallyNoetherian (U i); infer_instance
      let : ∀ i, QuasiCompact (C.f i) := by change ∀ i : ι, QuasiCompact (j i); infer_instance
      have hp' : ∀ i, J.comap (C.f i) ≤ I i ^ b := by
        intro i
        change J.comap (j i) ≤ I i ^ b
        rw [hL i]
        exact hp i
      have hs' : ∀ i, Smooth ((I i).subschemeι ≫ (C.f i ≫ f)) := by
        intro i
        change Smooth ((I i).subschemeι ≫ (j i ≫ f))
        rw [hg i]
        exact hs i
      have hbl' : ∀ i, Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase (I i) (hI i) ≫ (C.f i ≫ f)) := by
        intro i
        change Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase (I i) (hI i) ≫ (j i ≫ f))
        rw [hg i]
        exact hbl i
      obtain ⟨D, hD, he, hpD, hsD, hblD⟩ :=
        Blowups.Finite.OpenBlowupCenterGluing.Construction.exists_global_blowup_center_of_finite_open_data f J b C I hI hp' hs' hbl' hcompat
      change ∀ i : ι, D.comap (j i) = I i at he
      let U' := fun i => GlobalBlowup.Data.Construction.globalBlowup (I i) (hI i)
      let j' := fun i => GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo (j i) D (I i) (he i) hD (hI i)
      let g' := fun i => GlobalBlowup.Data.Construction.globalBlowupToBase (I i) (hI i) ≫ g i
      let L' := fun i => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (I i) (L i) (hI i) b
      let : ∀ i, IsIntegral (U' i) := fun i => inferInstanceAs (IsIntegral (GlobalBlowup.Data.Construction.globalBlowup (I i) (hI i)))
      let : ∀ i, IsLocallyNoetherian (U' i) := fun i => inferInstanceAs (IsLocallyNoetherian (GlobalBlowup.Data.Construction.globalBlowup (I i) (hI i)))
      let : ∀ i, IsOpenImmersion (j' i) := fun i => GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_isOpenImmersion (j i) D (I i) (he i) hD (hI i)
      let : ∀ i, QuasiCompact (j' i) := fun i => GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_quasiCompact (j i) D (I i) (he i) hD (hI i)
      have hg' : ∀ i, j' i ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase D hD ≫ f) = g' i := by
        intro i
        dsimp only [j', g']
        rw [← Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc, hg i]
      have hL' : ∀ i, (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal D J hD b).comap (j' i) = L' i := by
        intro i
        dsimp only [j', L']
        rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale, hL i]
      have hcover' : ∀ x : GlobalBlowup.Data.Construction.globalBlowup D hD, ∃ i y, j' i y = x :=
        (GlobalBlowup.OpenComparison.Construction.globalBlowupOpenCover D hD C I hI he).exists_eq
      have H' : ∀ i a, (tail i).OpenCompatible (tail a) (j' i) (j' a) := by
        intro i a
        have HH := H i a
        rw [hP i, hP a] at HH
        exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.OpenCompatible.tail (I i) (hI i) (hb i) (hp i) (hs i) (hbl i) (tail i)
          (I a) (hI a) (hb a) (hp a) (hs a) (hbl a) (tail a)
          (j i) (j a) D hD (he i) (he a) HH
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase D hD ≫ f) := hblD
      obtain ⟨Y, h, K, Q, r, hr⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup D hD) (GlobalBlowup.Data.Construction.globalBlowupToBase D hD ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal D J hD b) ι U' j' hcover' g' L' hg' hL' V k M tail htail H'
      obtain ⟨i, _, _⟩ := hcover (Classical.choice (inferInstance : Nonempty X))
      refine ⟨Y, h, K, .blowup D hD (hb i) hpD hsD hblD Q, r, ?_⟩
      intro a
      rw [hP a]
      exact (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff D hD (hb i) hpD hsD hblD Q
        (I a) (hI a) (hb a) (hp a) (hs a) (hbl a) (tail a) (j a) (r a)).mpr
          ⟨inferInstance, hg a, hL a, he a, hr a⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
