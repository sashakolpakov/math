import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DisjointCenterSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DisjointFactorBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComponentBoundaryAtlas

/-! # Sequence Compatibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual fixed-control sequences retaining every boundary label and common coordinates at each center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.boundaryAtlas
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} [Fintype β] {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ] :=
  ⟨A.indices, A.opens, A.cover, A.equations, A.component, A.boundary,
    fun i => Boundary.Schedule.Construction.boundaryFacesCover_univ (A.equations i)⟩

def Global.MonomialSequence.Construction.SmoothFixedControlSequence.boundaryCompatible
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J) :
    (β : Type) → [Fintype β] → (β → X.IdealSheafData) → Prop :=
  match T with
  | @Global.MonomialSequence.Construction.SmoothFixedControlSequence.terminal _ _ g _ _ _ => fun _ _ D => Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas g D [Finset.univ])
  | @Global.MonomialSequence.Construction.SmoothFixedControlSequence.blowup _ _ _ _ g _ I hI _ _ _ _ tail => fun β _ D =>
      Nonempty (Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g I D) ∧
        tail.boundaryCompatible (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)

theorem GlobalBoundary.SequenceCompatibility.Construction.exists_finite_disjoint_boundary_integral_center_sequence (N : ℕ) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
      (K : Fin N → X.IdealSheafData),
      (∀ i, K i ≠ ⊥) → (∀ i, IsIntegral (K i).subscheme) →
      (∀ i, Smooth ((K i).subschemeι ≫ f)) →
      (∀ i j, i ≠ j → K i ⊔ K j = ⊤) →
      (∀ i, J ≤ K i ^ (n + 1)) →
      (∏ i, K i) ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n →
      ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData),
        Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (∏ i, K i) D →
        ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J, T.integralCenters ∧ T.boundaryCompatible β D := by
  induction N with
  | zero =>
      intro X _ _ f _ J n K _ _ _ _ _ hprod β _ D A
      have ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤ := by
        simpa only [Fin.prod_univ_zero, Scheme.IdealSheafData.one_eq_top, top_le_iff] using hprod
      refine ⟨.terminal (by simpa only [Nat.add_sub_cancel] using ht), ?_, ?_⟩
      · change True
        trivial
      · change Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
        exact ⟨A.boundaryAtlas⟩
  | succ N ih =>
      intro X _ _ f _ J n K hK hInt hSm hDis hPerm hProd β _ D A
      let C := K 0
      let L := ∏ i : Fin N, K i.succ
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase C (hK 0)
      let : IsIntegral C.subscheme := hInt 0
      let : Smooth (C.subschemeι ≫ f) := hSm 0
      let : Smooth (π ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f C (hK 0)
      let J' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J (hK 0) (n + 1)
      let K' (i : Fin N) := (K i.succ).comap π
      let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C (hK 0) D
      have hfactorEq : (∏ i, K i) = C * L := Fin.prod_univ_succ K
      have hfactor : C * L ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n := hfactorEq ▸ hProd
      have hprod' : (∏ i, K' i) ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (π ≫ f) J' n := by
        have h := Global.FactorCenterDrop.Construction.global_factor_center_differential_bound f J C L (hK 0) n hfactor (hPerm 0)
        rw [Finite.DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod] at h
        exact h
      have hK' (i : Fin N) : K' i ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot C (K i.succ) (hK 0) (hK i.succ)
      have hInt' (i : Fin N) : IsIntegral (K' i).subscheme :=
        @Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_integral _ _ _ C (K i.succ) (hK 0)
          (hDis 0 i.succ (Fin.succ_ne_zero i).symm) (hInt i.succ)
      have hSm' (i : Fin N) : Smooth ((K' i).subschemeι ≫ (π ≫ f)) :=
        @Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_smooth _ _ _ _ f C (K i.succ) (hK 0)
          (hDis 0 i.succ (Fin.succ_ne_zero i).symm) (hSm i.succ)
      have hDis' (i j : Fin N) (hij : i ≠ j) : K' i ⊔ K' j = ⊤ := by
        change (K i.succ).comap π ⊔ (K j.succ).comap π = ⊤
        rw [← Scheme.IdealSheafData.comap_sup, hDis i.succ j.succ
          (fun h => hij (Fin.succ_injective _ h)), Scheme.IdealSheafData.comap_top]
      have hPerm' (i : Fin N) : J' ≤ K' i ^ (n + 1) :=
        Disjoint.CenterPermissibility.Construction.globalBlowup_preserves_disjoint_center_permissibility C (K i.succ) J (hK 0) (n + 1) (n + 1)
          (hDis i.succ 0 (Fin.succ_ne_zero i)) (hPerm i.succ)
      have hCL : C ⊔ L = ⊤ := Blowups.Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top C (fun i : Fin N => K i.succ) Finset.univ
        (fun i _ => hDis 0 i.succ (Fin.succ_ne_zero i).symm)
      have he : L.comap π = ∏ i, K' i := Finite.DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod (fun i : Fin N => K i.succ) Finset.univ π
      have A' : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (π ≫ f) (∏ i, K' i) D' :=
        he ▸ A.disjointFactorBlowup C L (hK 0) hfactorEq hCL
      obtain ⟨tail, htail, hboundary⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C (hK 0)) (π ≫ f) J' n K'
        hK' hInt' hSm' hDis' hPerm' hprod' (Option β) D' A'
      refine ⟨.blowup C (hK 0) (Nat.succ_pos n) (hPerm 0) (hSm 0) inferInstance tail, ⟨hInt 0, htail⟩, ?_⟩
      exact ⟨⟨A.comaximalFactor C L hfactorEq hCL⟩, hboundary⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
