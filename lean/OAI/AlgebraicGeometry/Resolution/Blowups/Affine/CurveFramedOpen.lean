import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FramedOpenControlTree
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFixedControlTree
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialOrderBound

/-! # Curve Framed Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFramedOpen.Construction

noncomputable section

/-! Finite fixed-control curve resolution with actual local coordinate frames at every center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]

/-- Every finite differential bound on a smooth affine curve produces a
finite tree of actual open refinements and coordinate-center blowups, with
the same prescribed positive control throughout and bounded blowup depth. -/
theorem exists_bounded_curve_framed_open_control_tree (b : ℕ) (hb : 0 < b) (n : ℕ) :
    ∀ (R : CommRingCat.{u}) [Algebra k R] [Algebra ℚ R] [IsNoetherianRing R]
      [Algebra.Smooth k R] (J : Ideal R), ringKrullDim R ≤ 1 →
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤ →
      ∃ T : FramedOpenControlTree.Construction.AffineFramedOpenControlTree k b R J, T.blowupDepth ≤ n := by
  classical
  induction n with
  | zero =>
      intro R _ _ _ _ J _ hbound
      have h := Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J (Nat.zero_le (b - 1))
      rw [hbound] at h
      exact ⟨.terminal (top_le_iff.mp h), Nat.zero_le _⟩
  | succ n ih =>
      intro R _ _ _ _ J hd hbound
      by_cases hbn : b ≤ n + 1
      · let I := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
        have hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤ :=
          (Curve.IntrinsicStep.Construction.first_iteratedRelativeDifferentialIdeal k J n).trans hbound
        obtain ⟨s, C, hcover⟩ := Curve.CenterFiniteFrameCover.Construction.exists_finite_curve_center_frame_cover k hd I hI
        have hchildren (i : s) : ∃ T : FramedOpenControlTree.Construction.AffineFramedOpenControlTree k b (C i).carrier
            (J.map (C i).map.toRingHom), T.blowupDepth ≤ n + 1 := by
          let S := (C i).carrier
          let f : R →ₐ[k] S := (C i).map
          let L := J.map f.toRingHom
          let : Algebra ℚ S := ((algebraMap k S).comp (algebraMap ℚ k)).toAlgebra
          let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
          have het : Etale (Spec.map (CommRingCat.ofHom f.toRingHom)) := inferInstance
          have hf : f.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
          have hdim : ringKrullDim S ≤ 1 :=
            (OpenDimension.Construction.ringKrullDim_le_of_spec_openImmersion f.toRingHom).trans hd
          have hnextbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L (n + 1) = ⊤ := by
            rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf J (n + 1), hbound, Ideal.map_top]
          have hmap : I.map f.toRingHom = Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n :=
            Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf J n
          rcases (C i).center with hunit | ⟨g, D, hgen, hD⟩
          · obtain ⟨T, hT⟩ := ih S L hdim (hmap.symm.trans hunit)
            exact ⟨T, hT.trans (Nat.le_succ n)⟩
          · let g' : ULift.{u} Unit → S := fun _ => g
            let D' : ULift.{u} Unit → Derivation k S S := fun _ => D
            have hframe : ∀ a c, D' a (g' c) = if a = c then 1 else 0 := by
              intro a c
              rw [ite_eq_left (Subsingleton.elim a c)]
              exact hD
            have hspan : Ideal.span (Set.range g') = Ideal.span {g} := by
              congr 1
              exact Set.range_const
            have hcenter : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n = Ideal.span (Set.range g') :=
              hmap.symm.trans (hgen.trans hspan.symm)
            obtain ⟨hperm, _, hπ, hdrop⟩ := CurveFixedControlStep.Construction.affine_curve_fixed_control_step k hdim L n b hb hbn hnextbound
            rw [hcenter] at hperm hπ hdrop
            let K := Ideal.span (Set.range g')
            let : IsIso (ReesGrading.Construction.affineBlowupToSpec K) := hπ
            have hleaf (j : ULift.{u} Unit) :
                ∃ T : FramedOpenControlTree.Construction.AffineFramedOpenControlTree k b
                  (.of (Blowup.Charts.Construction.blowupChart K ⟨g' j, Ideal.subset_span ⟨j, rfl⟩⟩))
                  (ControlledTransform.Construction.blowupControlledTransform K L b ⟨g' j, Ideal.subset_span ⟨j, rfl⟩⟩),
                  T.blowupDepth ≤ n := by
              let a : K := ⟨g' j, Ideal.subset_span ⟨j, rfl⟩⟩
              let : IsNoetherianRing (Blowup.Charts.Construction.blowupChart K a) := NoetherianCoordinateTransform.Construction.blowupChart_isNoetherian K a
              let : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart K a) := CurveChart.Construction.blowupChart_smooth_of_isIso k K a
              exact ih (.of (Blowup.Charts.Construction.blowupChart K a)) (ControlledTransform.Construction.blowupControlledTransform K L b a)
                ((OpenDimension.Construction.blowupChart_ringKrullDim_le_of_isIso K a).trans hdim) (hdrop a)
            refine ⟨.blowup (ULift.{u} Unit) g' D' hframe hb hperm (fun j => (hleaf j).choose), ?_⟩
            change (Finset.univ.sup fun j => (hleaf j).choose.blowupDepth) + 1 ≤ n + 1
            exact Nat.add_le_add_right (Finset.sup_le (fun j _ => (hleaf j).choose_spec)) 1
        have hsurj (p : PrimeSpectrum R) : ∃ i : s, ∃ q : PrimeSpectrum (C i).carrier,
            PrimeSpectrum.comap (C i).map.toRingHom q = p := by
          have hp : p ∈ ⨆ i, (C i).openRange := by rw [hcover]; trivial
          obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
          exact ⟨i, hi⟩
        refine ⟨.refineOpen s (fun i => (C i).carrier) (fun i => (C i).map)
          (fun i => (C i).isOpenImmersion) hsurj (fun i => (hchildren i).choose), ?_⟩
        change (Finset.univ.sup fun i => (hchildren i).choose.blowupDepth) ≤ n + 1
        exact Finset.sup_le (fun i _ => (hchildren i).choose_spec)
      · have h := Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J
          (show n + 1 ≤ b - 1 by omega)
        rw [hbound] at h
        exact ⟨.terminal (top_le_iff.mp h), Nat.zero_le _⟩

/-- In particular every nonzero ideal on a smooth integral affine curve
admits such a finite framed tree at every positive fixed control. -/
theorem exists_curve_framed_open_control_tree (b : ℕ) (hb : 0 < b)
    (R : CommRingCat.{u}) [Algebra k R] [IsDomain R] [Algebra.Smooth k R]
    (J : Ideal R) (hd : ringKrullDim R ≤ 1) (hJ : J ≠ ⊥) :
    Nonempty (FramedOpenControlTree.Construction.AffineFramedOpenControlTree k b R J) := by
  let : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨n, hn⟩ := Blowups.Smooth.DifferentialOrderBound.Construction.exists_smooth_relative_differential_order_bound k J hJ
  obtain ⟨T, _⟩ := exists_bounded_curve_framed_open_control_tree k b hb n R J hd hn
  exact ⟨T⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFramedOpen.Construction
