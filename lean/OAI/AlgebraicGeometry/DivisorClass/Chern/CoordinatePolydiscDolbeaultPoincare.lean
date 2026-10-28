import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePullbackIdentities
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscUpdate
import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormBasis

/-! # Coordinate Polydisc Dolbeault Poincare -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

noncomputable section

section

/-! Actual form transport to one selected coordinate and back to a smaller polydisc. -/

open _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def coordinateFormToProduct (U : ι → Opens ℂ) (i : ι) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc U) n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (OneFormCauchyElimination.complexProductOpen (Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) (U i)) n :=
  Complex.LinearOpenPullback.complexLinearOpenPullback (Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap
    (Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i)

def coordinateFormFromProduct (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (OneFormCauchyElimination.complexProductOpen (Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W) n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)) n :=
  Complex.LinearOpenPullback.complexLinearOpenPullback (Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
    (CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W)

theorem coordinateFormFromProduct_d (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (OneFormCauchyElimination.complexProductOpen
      (Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W) n) :
    coordinateFormFromProduct U i W (DolbeaultOpen.openDolbeaultD n a) =
      DolbeaultOpen.openDolbeaultD n (coordinateFormFromProduct U i W a) :=
  (Complex.LinearOpenPullback.openDolbeaultD_complexLinearPullback _ _ a).symm

theorem coordinateFormFromProduct_restrict_inverse (U : ι → Opens ℂ) (i : ι)
    (W : Opens ℂ) (hW : W ≤ U i) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc U) n) :
    coordinateFormFromProduct U i W
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (OneFormCauchyElimination.complexProductOpen_mono hW) (coordinateFormToProduct U i a)) =
        Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (CoordinatePolydiscUpdate.coordinatePolydisc_update_le U i W hW) a :=
  CoordinatePullbackIdentities.complexLinearOpenPullback_inverse_restrict (Complex.CoordinateSplit.splitComplexCoordinate i)
    (Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) (CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W)
    (CoordinatePolydiscUpdate.coordinatePolydisc_update_le U i W hW) (OneFormCauchyElimination.complexProductOpen_mono hW) a

theorem coordinateFormFromProduct_coefficient_same (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (OneFormCauchyElimination.complexProductOpen
      (Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W) 1)
    (x : Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)) :
    AntiOneFormCoordinates.oneFormLinear (coordinateFormFromProduct U i W a x) (AntiOneFormBasis.complexCoordinateVector i) =
      AntiOneFormCoordinates.oneFormLinear (a ⟨Complex.CoordinateSplit.splitComplexCoordinate i x, CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W x.property⟩)
        (0, 1) := by
  have hc := CoordinatePullbackIdentities.complexLinearOpenPullback_oneFormCoefficient (Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
    (CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W) a x (AntiOneFormBasis.complexCoordinateVector i)
  exact hc.trans (congrArg
    (fun v => AntiOneFormCoordinates.oneFormLinear (a ⟨Complex.CoordinateSplit.splitComplexCoordinate i x,
      CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W x.property⟩) v) (AntiOneFormBasis.splitComplexCoordinate_vector_same i))

theorem coordinateFormToProduct_zero_other (U : ι → Opens ℂ) (i j : ι) (hji : j ≠ i)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc U) 1)
    (ha : ∀ x : Complex.CoordinateSplit.coordinatePolydisc U, AntiOneFormCoordinates.oneFormLinear (a x) (AntiOneFormBasis.complexCoordinateVector j) = 0) :
    ∀ x : OneFormCauchyElimination.complexProductOpen (Complex.CoordinateSplit.coordinatePolydisc (fun k : {k : ι // k ≠ i} => U k)) (U i),
      AntiOneFormCoordinates.oneFormLinear (coordinateFormToProduct U i a x)
        ((fun k : {k : ι // k ≠ i} => AntiOneFormBasis.complexCoordinateVector j k), 0) = 0 := by
  intro x
  have hc := CoordinatePullbackIdentities.complexLinearOpenPullback_oneFormCoefficient (Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap
    (Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) a x
      ((fun k : {k : ι // k ≠ i} => AntiOneFormBasis.complexCoordinateVector j k), 0)
  have hinv : (Complex.CoordinateSplit.splitComplexCoordinate i).symm
      ((fun k : {k : ι // k ≠ i} => AntiOneFormBasis.complexCoordinateVector j k), 0) = AntiOneFormBasis.complexCoordinateVector j := by
    rw [← AntiOneFormBasis.splitComplexCoordinate_vector_other i j hji, ContinuousLinearEquiv.symm_apply_apply]
  let y : Complex.CoordinateSplit.coordinatePolydisc U := ⟨(Complex.CoordinateSplit.splitComplexCoordinate i).symm x,
    Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i x.property⟩
  exact hc.trans ((congrArg (fun v => AntiOneFormCoordinates.oneFormLinear (a y) v) hinv).trans (ha y))

theorem coordinateFormFromProduct_coefficient_other (U : ι → Opens ℂ) (i j : ι) (hji : j ≠ i)
    (W : Opens ℂ) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (OneFormCauchyElimination.complexProductOpen
      (Complex.CoordinateSplit.coordinatePolydisc (fun k : {k : ι // k ≠ i} => U k)) W) 1)
    (x : Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)) :
    AntiOneFormCoordinates.oneFormLinear (coordinateFormFromProduct U i W a x) (AntiOneFormBasis.complexCoordinateVector j) =
      AntiOneFormCoordinates.oneFormLinear (a ⟨Complex.CoordinateSplit.splitComplexCoordinate i x, CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W x.property⟩)
        ((fun k : {k : ι // k ≠ i} => AntiOneFormBasis.complexCoordinateVector j k), 0) := by
  have hc := CoordinatePullbackIdentities.complexLinearOpenPullback_oneFormCoefficient (Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
    (CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W) a x (AntiOneFormBasis.complexCoordinateVector j)
  exact hc.trans (congrArg
    (fun v => AntiOneFormCoordinates.oneFormLinear (a ⟨Complex.CoordinateSplit.splitComplexCoordinate i x,
      CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W x.property⟩) v) (AntiOneFormBasis.splitComplexCoordinate_vector_other i j hji))

end

section

/-! Remove any selected coordinate coefficient of an actual pure closed one-form on a finite polydisc. -/

open _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_polydisc_coefficient_elimination (U : ι → Opens ℂ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc U) 1) (ha : DolbeaultOpen.openDolbeaultD 1 a = 0)
    (hpure : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) (x : Complex.CoordinateSplit.coordinatePolydisc U) (i : ι) :
    ∃ W : Opens ℂ, x.val i ∈ W ∧ ∃ hW : W ≤ U i,
      ∃ b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)) 1,
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)) 0,
        b + DolbeaultOpen.openDolbeaultD 0 t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (CoordinatePolydiscUpdate.coordinatePolydisc_update_le U i W hW) a ∧
          DolbeaultOpen.openDolbeaultD 1 b = 0 ∧ Open.DolbeaultPrime.OpenFormHasBidegree 0 1 b ∧
          (∀ y : Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W),
            AntiOneFormCoordinates.oneFormLinear (b y) (AntiOneFormBasis.complexCoordinateVector i) = 0) ∧
          (∀ j : ι, j ≠ i →
            (∀ y : Complex.CoordinateSplit.coordinatePolydisc U, AntiOneFormCoordinates.oneFormLinear (a y) (AntiOneFormBasis.complexCoordinateVector j) = 0) →
            ∀ y : Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W),
              AntiOneFormCoordinates.oneFormLinear (b y) (AntiOneFormBasis.complexCoordinateVector j) = 0) := by
  let S := Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)
  let A : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (OneFormCauchyElimination.complexProductOpen S (U i)) 1 := coordinateFormToProduct U i a
  have hA : DolbeaultOpen.openDolbeaultD 1 A = 0 := CoordinatePullbackIdentities.complexLinearOpenPullback_closed
    (Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap (Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) a ha
  have hAp : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 A := Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree
    (Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap (Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) hpure
  obtain ⟨W, hxW, hW, g, hg, hB, hBp, hBzero, hBprior⟩ :=
    OneFormCauchyElimination.exists_oneForm_coefficient_elimination A hA hAp ((Complex.CoordinateSplit.mem_coordinatePolydisc U x).mp x.property i)
  let B := DolbeaultOneFormCorrection.correctDolbeaultOneForm (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (OneFormCauchyElimination.complexProductOpen_mono hW) A) g hg
  let b := coordinateFormFromProduct U i W B
  let t := coordinateFormFromProduct U i W (ScalarDolbeaultCommutation.scalarOpenZeroForm (OneFormCauchyElimination.complexProductOpen S W) g hg)
  have hsum : b + DolbeaultOpen.openDolbeaultD 0 t =
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (CoordinatePolydiscUpdate.coordinatePolydisc_update_le U i W hW) a := by
    have hs := congrArg (coordinateFormFromProduct U i W)
      (CoordinatePullbackIdentities.correctDolbeaultOneForm_add_dbar (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (OneFormCauchyElimination.complexProductOpen_mono hW) A) hg)
    rw [(coordinateFormFromProduct U i W).map_add, coordinateFormFromProduct_d] at hs
    dsimp only [A] at hs
    rw [coordinateFormFromProduct_restrict_inverse U i W hW a] at hs
    exact hs
  refine ⟨W, hxW, hW, b, t, hsum,
    CoordinatePullbackIdentities.complexLinearOpenPullback_closed (Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
      (CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W) B hB,
    Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree (Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
      (CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W) hBp, ?_, ?_⟩
  · intro y
    exact (coordinateFormFromProduct_coefficient_same U i W B y).trans (hBzero _)
  · intro j hji hj y
    exact (coordinateFormFromProduct_coefficient_other U i j hji W B y).trans
      (hBprior (fun k : {k : ι // k ≠ i} => AntiOneFormBasis.complexCoordinateVector j k)
        (coordinateFormToProduct_zero_other U i j hji a hj) _)

end

section

/-! Finite iteration of the actual Cauchy coefficient-elimination step. -/

open _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem coordinatePolydisc_mono (U V : ι → Opens ℂ) (h : ∀ i, V i ≤ U i) :
    Complex.CoordinateSplit.coordinatePolydisc V ≤ Complex.CoordinateSplit.coordinatePolydisc U := by
  intro x hx
  exact (Complex.CoordinateSplit.mem_coordinatePolydisc U x).mpr (fun i => h i ((Complex.CoordinateSplit.mem_coordinatePolydisc V x).mp hx i))

omit [Fintype ι] in
theorem coordinateOpen_update_le (V : ι → Opens ℂ) (i : ι) (W : Opens ℂ) (hW : W ≤ V i) :
    ∀ j, Function.update V i W j ≤ V j := by
  intro j
  by_cases h : j = i
  · subst j
    simpa only [Function.update_self] using hW
  · rw [Function.update_of_ne h]

theorem exists_polydisc_eliminate_finset (U : ι → Opens ℂ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc U) 1) (ha : DolbeaultOpen.openDolbeaultD 1 a = 0)
    (hpure : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) (x : Complex.CoordinateSplit.coordinatePolydisc U) (s : Finset ι) :
    ∃ V : ι → Opens ℂ, ∃ hVU : ∀ i, V i ≤ U i, x.val ∈ Complex.CoordinateSplit.coordinatePolydisc V ∧
      ∃ b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc V) 1, ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc V) 0,
        b + DolbeaultOpen.openDolbeaultD 0 t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (coordinatePolydisc_mono U V hVU) a ∧
          DolbeaultOpen.openDolbeaultD 1 b = 0 ∧ Open.DolbeaultPrime.OpenFormHasBidegree 0 1 b ∧
            ∀ i ∈ s, ∀ y : Complex.CoordinateSplit.coordinatePolydisc V, AntiOneFormCoordinates.oneFormLinear (b y) (AntiOneFormBasis.complexCoordinateVector i) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨U, fun i => le_refl (U i), x.property, a, 0, ?_, ha, hpure, ?_⟩
      · rw [(DolbeaultOpen.openDolbeaultD (U := Complex.CoordinateSplit.coordinatePolydisc U) 0).map_zero, add_zero]
        exact (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_refl a).symm
      · intro i hi
        exact False.elim (Finset.notMem_empty i hi)
  | @insert i s hi ih =>
      obtain ⟨V, hVU, hxV, b, t, hsum, hb, hbp, hzero⟩ := ih
      obtain ⟨W, hxW, hWV, c, u, hstep, hc, hcp, hci, hcprior⟩ :=
        exists_polydisc_coefficient_elimination V b hb hbp ⟨x, hxV⟩ i
      let V' := Function.update V i W
      let hnew := CoordinatePolydiscUpdate.coordinatePolydisc_update_le V i W hWV
      have hV'U : ∀ j, V' j ≤ U j := fun j => (coordinateOpen_update_le V i W hWV j).trans (hVU j)
      let t' : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc V') 0 := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew t + u
      have hsum' : c + DolbeaultOpen.openDolbeaultD 0 t' =
          Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (coordinatePolydisc_mono U V' hV'U) a := by
        have hrestrict := congrArg (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (n := 1) hnew) hsum
        rw [(Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (n := 1) hnew).map_add,
          DolbeaultZeroKernelMap.openDolbeaultD_restrict, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans] at hrestrict
        calc
          c + DolbeaultOpen.openDolbeaultD 0 t' =
              (c + DolbeaultOpen.openDolbeaultD 0 u) + DolbeaultOpen.openDolbeaultD 0 (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew t) := by
            change c + DolbeaultOpen.openDolbeaultD 0 (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew t + u) = _
            rw [map_add]
            abel
          _ = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew b + DolbeaultOpen.openDolbeaultD 0 (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hnew t) := by rw [hstep]
          _ = _ := hrestrict
      refine ⟨V', hV'U, CoordinatePolydiscUpdate.coordinatePolydisc_update_mem V i W x hxV hxW, c, t', hsum', hc, hcp, ?_⟩
      intro j hj y
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        exact hci y
      · exact hcprior j (fun hji => hi (hji ▸ hjs)) (hzero j hjs) y

theorem exists_polydisc_dolbeault_primitive (U : ι → Opens ℂ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc U) 1) (ha : DolbeaultOpen.openDolbeaultD 1 a = 0)
    (hpure : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) (x : Complex.CoordinateSplit.coordinatePolydisc U) :
    ∃ V : ι → Opens ℂ, ∃ hVU : ∀ i, V i ≤ U i, x.val ∈ Complex.CoordinateSplit.coordinatePolydisc V ∧
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (Complex.CoordinateSplit.coordinatePolydisc V) 0,
        DolbeaultOpen.openDolbeaultD 0 t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (coordinatePolydisc_mono U V hVU) a := by
  obtain ⟨V, hVU, hxV, b, t, hsum, _, hbp, hzero⟩ := exists_polydisc_eliminate_finset U a ha hpure x Finset.univ
  have hbzero := AntiOneFormBasis.antiOneForm_eq_zero_of_basis_coefficients b hbp (fun y i => hzero i (Finset.mem_univ i) y)
  refine ⟨V, hVU, hxV, t, ?_⟩
  simpa only [hbzero, zero_add] using hsum

end

section

/-! Local Dolbeault exactness for actual `(0,1)` forms on arbitrary finite-coordinate open domains. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem exists_coordinatePolydisc_neighborhood (O : Opens (ι → ℂ)) (x : O) :
    ∃ U : ι → Opens ℂ, x.val ∈ Complex.CoordinateSplit.coordinatePolydisc U ∧ Complex.CoordinateSplit.coordinatePolydisc U ≤ O := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (O.isOpen.mem_nhds x.property)
  let U : ι → Opens ℂ := fun i => ⟨ball (x.val i) r, isOpen_ball⟩
  refine ⟨U, (Complex.CoordinateSplit.mem_coordinatePolydisc U x).mpr (fun _ => mem_ball_self hr), ?_⟩
  intro y hy
  apply hsub
  rw [ball_pi _ hr]
  intro i _
  exact (Complex.CoordinateSplit.mem_coordinatePolydisc U y).mp hy i

theorem coordinateDolbeaultPoincare_one (O : Opens (ι → ℂ)) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm O 1)
    (ha : DolbeaultOpen.openDolbeaultD 1 a = 0) (hpure : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) (x : O) :
    ∃ W : Opens (ι → ℂ), x.val ∈ W ∧ ∃ hW : W ≤ O,
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W 0, DolbeaultOpen.openDolbeaultD 0 t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hW a := by
  obtain ⟨U, hxU, hUO⟩ := exists_coordinatePolydisc_neighborhood O x
  let ar := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hUO a
  have har : DolbeaultOpen.openDolbeaultD 1 ar = 0 := by
    change DolbeaultOpen.openDolbeaultD 1 (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hUO a) = 0
    rw [← DolbeaultZeroKernelMap.openDolbeaultD_restrict hUO a, ha]
    exact (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hUO).map_zero
  have harp : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 ar := Open.DolbeaultPrime.openFormHasBidegree_restrict hUO hpure
  obtain ⟨V, hVU, hxV, t, ht⟩ := exists_polydisc_dolbeault_primitive U ar har harp ⟨x, hxU⟩
  refine ⟨Complex.CoordinateSplit.coordinatePolydisc V, hxV, (coordinatePolydisc_mono U V hVU).trans hUO, t, ?_⟩
  exact ht.trans (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans hUO (coordinatePolydisc_mono U V hVU) a)

end

/-! Genuine local Dolbeault exactness in degree one on finite-dimensional complex chart models. -/

open _root_.TopologicalSpace Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem localDolbeaultPoincare_one (O : Opens E) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm O 1)
    (ha : DolbeaultOpen.openDolbeaultD 1 a = 0) (hpure : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) (x : O) :
    ∃ V : Opens E, x.val ∈ V ∧ ∃ hV : V ≤ O,
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V 0, DolbeaultOpen.openDolbeaultD 0 t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hV a := by
  let n := Module.finrank ℂ E
  let e : (Fin n → ℂ) ≃L[ℂ] E := (Module.finBasis ℂ E).equivFun.symm.toContinuousLinearEquiv
  let U : Opens (Fin n → ℂ) := ⟨e ⁻¹' (O : Set E), O.isOpen.preimage e.continuous⟩
  have hmap : MapsTo e (U : Set (Fin n → ℂ)) (O : Set E) := fun _ hy => hy
  let A := Complex.LinearOpenPullback.complexLinearOpenPullback e.toContinuousLinearMap hmap a
  have hA : DolbeaultOpen.openDolbeaultD 1 A = 0 := CoordinatePullbackIdentities.complexLinearOpenPullback_closed e.toContinuousLinearMap hmap a ha
  have hAp : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 A := Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree e.toContinuousLinearMap hmap hpure
  let y : U := ⟨e.symm x, by
    change e (e.symm x) ∈ O
    simpa only [e.apply_symm_apply] using x.property⟩
  obtain ⟨W, hyW, hW, t, ht⟩ := coordinateDolbeaultPoincare_one U A hA hAp y
  let V : Opens E := ⟨e '' (W : Set (Fin n → ℂ)), e.toHomeomorph.isOpenMap _ W.isOpen⟩
  have hVO : V ≤ O := by
    rintro z ⟨u, hu, rfl⟩
    exact hW hu
  have hInv : MapsTo e.symm (V : Set E) (W : Set (Fin n → ℂ)) := by
    rintro z ⟨u, hu, rfl⟩
    simpa only [e.symm_apply_apply] using hu
  let t' := Complex.LinearOpenPullback.complexLinearOpenPullback e.symm.toContinuousLinearMap hInv t
  refine ⟨V, ⟨e.symm x, hyW, e.apply_symm_apply x⟩, hVO, t', ?_⟩
  have hd := Complex.LinearOpenPullback.openDolbeaultD_complexLinearPullback e.symm.toContinuousLinearMap hInv t
  have htransport := congrArg (Complex.LinearOpenPullback.complexLinearOpenPullback e.symm.toContinuousLinearMap hInv) ht
  have hroundtrip := CoordinatePullbackIdentities.complexLinearOpenPullback_inverse_restrict e.symm hmap hInv hVO hW a
  exact hd.trans (htransport.trans hroundtrip)

theorem pureLocalDolbeaultPoincare_one (O : Opens E) (a : Open.DolbeaultPrime.AntiOpenForm O 1)
    (ha : Open.DolbeaultPrime.pureOpenDolbeaultD O 1 a = 0) (x : O) :
    ∃ V : Opens E, x.val ∈ V ∧ ∃ hV : V ≤ O,
      ∃ t : Open.DolbeaultPrime.AntiOpenForm V 0, Open.DolbeaultPrime.pureOpenDolbeaultD V 0 t = Open.DolbeaultPrime.antiOpenFormRestrict hV a := by
  have hclosed : DolbeaultOpen.openDolbeaultD 1 a.1 = 0 := congrArg Subtype.val ha
  obtain ⟨V, hxV, hV, t, ht⟩ := localDolbeaultPoincare_one O a.1 hclosed a.2 x
  refine ⟨V, hxV, hV, ⟨t, fun y => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E (t y)⟩, ?_⟩
  exact Subtype.ext ht

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare
