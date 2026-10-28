import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceTreeCover
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementCoefficientData
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.GeneratedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientTerminalBound
import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianCoordinateTransform

/-! # Open Coefficient Tree Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.OpenCoefficientTreeLift.Construction

noncomputable section

/-! Lifting finite framed coefficient trees with open refinements to actual smooth ambient trees. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra
  Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale
  EtaleLine.ReferenceBase.Construction.etaleLineChart_originalScalarTower EtaleLine.HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]

/-- A finite actual coefficient tree at factorial control lifts, without
increasing depth, to a finite tree of permissible smooth ambient blowups.
The exact retained coefficient ideal is carried through every branch. -/
theorem exists_lifted_framed_open_coefficient_tree {n : ℕ}
    {H : CommRingCat.{u}} [Algebra k H] {B : Ideal H}
    (T : Affine.FramedOpenControlTree.Construction.AffineFramedOpenControlTree k (n + 1).factorial H B) :
    ∀ [Algebra.Smooth k H] (R : CommRingCat.{u})
      [Algebra k R] [Algebra H R] [IsScalarTower k H R]
      [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
      [Algebra.Smooth k R] [IsNoetherianRing R] [Algebra ℚ R]
      (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
      {τ : Type u} (p : τ → R) (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X})),
      C.map e.toRingHom = B →
      WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
        (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
        (algebraMap H[X] R X) p (n + 1) ≤ C →
      C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1) →
      algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n →
      ∃ S : Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R (Ideal.span (Set.range p)), S.blowupDepth ≤ T.blowupDepth := by
  classical
  induction T with
  | @terminal H _ B ht =>
      intro _ R _ _ _ _ _ _ _ _ _ e τ p C hC _ hupp hz
      have hterminal := Blowups.Smooth.CoefficientTerminalBound.Construction.retracted_coefficient_terminal_bound_clears_order k
        (algebraMap H[X] R X) (Ideal.span (Set.range p)) n hz e.toRingEquiv C hupp
        (by simpa only [hC] using ht)
      refine ⟨.terminal (by simpa only [Nat.add_sub_cancel] using hterminal), ?_⟩
      exact Nat.zero_le _
  | @refineOpen H _ B ι _ A aA φ hφ hcover children ih =>
      intro _ R _ _ _ _ _ _ _ _ _ e τ p C hC hlow hupp hz
      have hφe (i : ι) : (φ i).toRingHom.Etale := by
        let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ i).toRingHom)) := hφ i
        have he : Etale (Spec.map (CommRingCat.ofHom (φ i).toRingHom)) := inferInstance
        exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp he
      have hdata (i : ι) := EtaleLine.RefinementCoefficientData.Construction.exists_etale_line_refined_coefficient_data k
        (φ i) (hφe i) e p n C hlow hupp hz
      choose V akV aAV aAPV hkAV hAPV heV hsV f hf hcoord e' C' hl hu hC' hz' hcomm using hdata
      let : ∀ i, Algebra k (V i) := akV
      let : ∀ i, Algebra (A i) (V i) := aAV
      let : ∀ i, Algebra (A i)[X] (V i) := aAPV
      let : ∀ i, IsScalarTower k (A i) (V i) := hkAV
      let : ∀ i, IsScalarTower (A i) (A i)[X] (V i) := hAPV
      let : ∀ i, Algebra.Etale (A i)[X] (V i) := heV
      let : ∀ i, Algebra.Smooth k (V i) := hsV
      have hchildren (i : ι) : ∃ S : Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1)
          (V i) ((Ideal.span (Set.range p)).map (f i).toRingHom),
          S.blowupDepth ≤ (children i).blowupDepth := by
        let : Algebra.Smooth k (A i) := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k (φ i) (hφe i)
        let : IsNoetherianRing (V i) := Algebra.FiniteType.isNoetherianRing k (V i)
        let : Algebra ℚ (V i) := ((algebraMap k (V i)).comp (algebraMap ℚ k)).toAlgebra
        have hp : (Ideal.span (Set.range p)).map (f i).toRingHom =
            Ideal.span (Set.range (fun t => f i (p t))) := by
          rw [Ideal.map_span, ← Set.range_comp]
          rfl
        rw [hp]
        exact ih i (V i) (e' i) (fun t => f i (p t)) (C' i)
          (by simpa only [hC] using hC' i) (hl i) (hu i) (hz' i)
      let ρ := e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}))
      have hρ : Function.Surjective ρ := e.surjective.comp Ideal.Quotient.mk_surjective
      let ρ' (i : ι) := (e' i).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap (A i)[X] (V i) X}))
      have hcove (q : PrimeSpectrum R) (hq : algebraMap H[X] R X ∈ q.asIdeal) :
          ∃ i, ∃ q' : PrimeSpectrum (V i), PrimeSpectrum.comap (f i).toRingHom q' = q := by
        have hker : RingHom.ker ρ ≤ q.asIdeal := by
          intro x hx
          change e (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}) x) = 0 at hx
          have hx' : Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}) x = 0 :=
            e.injective (by simpa only [map_zero] using hx)
          exact ((Ideal.span_singleton_le_iff_mem q.asIdeal).mpr hq)
            (Ideal.Quotient.eq_zero_iff_mem.mp hx')
        exact Blowups.Etale.RefinementHelpers.Construction.retraction_square_cover_lifts ρ hρ A V (fun i => (φ i).toRingHom)
          (fun i => (f i).toRingHom) ρ' hcomm hcover q hker
      exact Blowups.Etale.HypersurfaceTreeCover.Construction.exists_control_tree_of_hypersurface_cover k R (Ideal.span (Set.range p))
        (algebraMap H[X] R X) n (Finset.univ.sup fun i => (children i).blowupDepth) hz
        ι V f hf hcove (fun i => (hchildren i).choose)
        (fun i => (hchildren i).choose_spec.trans
          (Finset.le_sup (f := fun i : ι => (children i).blowupDepth) (Finset.mem_univ i)))
  | @blowup H _ B ι _ _ g δ hδ hb hperm children ih =>
      intro _ R _ _ _ _ _ _ _ _ _ e τ p C hC hlow hupp hz
      let K := Ideal.span (Set.range g)
      let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
      obtain ⟨hp, hsmooth, hblowup⟩ := EtaleLine.FrameCoefficientStep.Construction.etaleLine_frame_coefficient_center k e p (n + 1)
        g δ hδ C hlow (by simpa only [hC] using hperm)
      let : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := hblowup
      let : Smooth (ReesGrading.Construction.affineBlowupToSpec K ≫ Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
        DualFrameBlowupSmooth.Construction.dual_derivation_family_blowup_smooth g δ hδ
      have hchildren (i : ι) :
          ∃ S : Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1)
            (.of (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩))
            (ControlledTransform.Construction.blowupControlledTransform I (Ideal.span (Set.range p)) (n + 1)
              (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator K ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩)),
            S.blowupDepth ≤ (children i).blowupDepth := by
        let a : K := ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩
        let : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart K a) := Blowups.Smooth.BlowupChart.Construction.blowupChart_smooth_of_blowup_smooth k K a
        let : Algebra.Smooth k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a) :=
          Blowups.Smooth.BlowupChart.Construction.blowupChart_smooth_of_blowup_smooth k I (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
        let : IsNoetherianRing (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a) :=
          NoetherianCoordinateTransform.Construction.blowupChart_isNoetherian I (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
        obtain ⟨e', C', hlow', hupp', hC', hz'⟩ :=
          EtaleLine.PersistentCoefficientStep.Construction.etaleLine_persistent_coefficient_chart k e K a p n hp hz C hlow hupp
        rw [ControlledGeneratorFamily.Construction.blowupControlledTransform_eq_span_family I p _ (n + 1) hp]
        exact ih i (.of (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)) e'
          (ControlledGeneratorFamily.Construction.blowupChartTransformFamily I p (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (n + 1) hp)
          C' (by simpa only [hC] using hC') hlow' hupp' hz'
      let next : ∀ j : Option ι, Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1)
          (.of (Blowup.Charts.Construction.blowupChart I (EtaleLine.FamilyCover.Construction.etaleLineFamilyChartGenerator (R := R) g j)))
          (ControlledTransform.Construction.blowupControlledTransform I (Ideal.span (Set.range p)) (n + 1)
            (EtaleLine.FamilyCover.Construction.etaleLineFamilyChartGenerator (R := R) g j)) := by
        intro j
        cases j with
        | none =>
            dsimp only [EtaleLine.FamilyCover.Construction.etaleLineFamilyChartGenerator]
            exact .terminal (by simpa only [Nat.add_sub_cancel] using
              EtaleLine.PersistentCoefficientStep.Construction.etaleLine_normal_chart_terminal k K (Ideal.span (Set.range p)) n hp hz)
        | some i => exact (hchildren i).choose
      refine ⟨.blowup I (Nat.succ_pos n) hp hsmooth hblowup (Option ι)
        (EtaleLine.FamilyCover.Construction.etaleLineFamilyChartGenerator g) (EtaleLine.GeneratedFrame.Construction.etaleLineGeneratedFrameDerivation k δ)
        (EtaleLine.GeneratedFrame.Construction.etaleLineGeneratedChartFamily_dual k K (fun i => ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩) δ hδ)
        (EtaleLine.FamilyCover.Construction.etaleLineFamilyChartGenerator_span g) next, ?_⟩
      change (Finset.univ.sup fun j => (next j).blowupDepth) + 1 ≤
        (Finset.univ.sup fun i => (children i).blowupDepth) + 1
      apply Nat.add_le_add_right
      apply Finset.sup_le
      intro j _
      cases j with
      | none => exact Nat.zero_le _
      | some i =>
          exact (hchildren i).choose_spec.trans
            (Finset.le_sup (f := fun i : ι => (children i).blowupDepth) (Finset.mem_univ i))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.OpenCoefficientTreeLift.Construction
