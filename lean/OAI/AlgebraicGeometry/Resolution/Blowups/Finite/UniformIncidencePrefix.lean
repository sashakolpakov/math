import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.IncidencePersistence
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DisjointControlPrefix

/-! # Uniform Incidence Prefix -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Prescribed disjoint incidence groups give constant boundary incidence at every actual step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible_of_finite_disjoint_centers (N : ℕ) :
    ∀ {b : ℕ} {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
      {Y : Scheme} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : Y.IdealSheafData}
      (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g L) (I : X.IdealSheafData) (K : Fin N → X.IdealSheafData),
      (∀ i, K i ≠ ⊥) → (∀ i j, i ≠ j → K i ⊔ K j = ⊤) → I = ∏ i, K i →
      ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
        (F : Fin N → Finset β),
      (∀ j i, (K j).ideal (A.opens i) ≠ ⊤ → A.divided i = F j) →
      P.followsCenters (List.ofFn K) → P.uniformBoundaryCompatible β D := by
  induction N with
  | zero =>
      intro b X _ _ f J Y g L P I K _ _ _ β _ D A _ _ hP
      cases P with
      | stop => exact ⟨A.boundaryAtlas⟩
      | blowup C hC hb hp hs hbl tail =>
          obtain ⟨cs, he, _⟩ := hP
          rw [List.ofFn_zero] at he
          cases he
  | succ N ih =>
      intro b X _ _ f J Y g L P I K hK hDis hfactor β _ D A F hF hP
      cases P with
      | stop =>
          change List.ofFn K = [] at hP
          rw [List.ofFn_succ] at hP
          cases hP
      | blowup C hC hb hp hs hbl tail =>
          obtain ⟨cs, he, htail⟩ := hP
          rw [List.ofFn_succ] at he
          have hCeq : K 0 = C := (List.cons.inj he).1
          have hcs : List.ofFn (fun i : Fin N => K i.succ) = cs := (List.cons.inj he).2
          subst C
          subst cs
          let R := ∏ i : Fin N, K i.succ
          have hCR : K 0 ⊔ R = ⊤ := Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top (K 0)
            (fun i : Fin N => K i.succ) Finset.univ
            (fun i _ => hDis 0 i.succ (Fin.succ_ne_zero i).symm)
          have hprod : I = K 0 * R := hfactor.trans (Fin.prod_univ_succ K)
          let AC := (A.comaximalFactor (K 0) R hprod hCR).withUniformIncidence (F 0) (hF 0)
          let π := GlobalBlowup.Data.Construction.globalBlowupToBase (K 0) hC
          let K' (i : Fin N) := (K i.succ).comap π
          have hK' (i : Fin N) : K' i ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot (K 0) (K i.succ) hC (hK i.succ)
          have hDis' (i j : Fin N) (hij : i ≠ j) : K' i ⊔ K' j = ⊤ := by
            change (K i.succ).comap π ⊔ (K j.succ).comap π = ⊤
            rw [← Scheme.IdealSheafData.comap_sup, hDis i.succ j.succ
              (fun he => hij (Fin.succ_injective _ he)), Scheme.IdealSheafData.comap_top]
          have hR : R.comap π = ∏ i, K' i :=
            Finite.DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod (fun i : Fin N => K i.succ) Finset.univ π
          let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (K 0) hC D
          let A' := A.disjointFactorBlowup (K 0) R hC hprod hCR
          let F' (i : Fin N) := (F i.succ).map Function.Embedding.some
          have hF' : ∀ j i, (K' j).ideal (A'.opens i) ≠ ⊤ → A'.divided i = F' j := by
            intro j i hp
            exact A.disjointFactorBlowup_incidence (K 0) R hC hprod hCR (K j.succ) (F j.succ) (hF j.succ) i hp
          rw [List.map_ofFn] at htail
          have ht := ih tail (R.comap π) K' hK' hDis' hR (Option β) D' A' F' hF' htail
          exact ⟨⟨AC, F 0, fun _ => rfl⟩, ht⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
