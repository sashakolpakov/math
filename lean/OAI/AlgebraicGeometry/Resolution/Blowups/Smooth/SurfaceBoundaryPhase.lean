import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ControlPhaseTree
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceOrderTree
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.MaximumOrderTransform

/-! # Surface Boundary Phase -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceBoundaryPhase.Construction

noncomputable section

/-! Finite actual boundary-intersection clearance phases on smooth affine surfaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]

/-- An actual auxiliary control tree yields a boundary phase of the same
depth. Every center's marked permissibility and containment in the
selected boundary intersection are derived from its actual dual frame. -/
theorem exists_boundary_control_phase_of_tree (m : ℕ) (hm : 0 < m)
    {R : CommRingCat.{u}} [Algebra k R] {K : Ideal R}
    (T : AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k m R K) :
    ∀ [Algebra.Smooth k R] (J L : Ideal R), K = Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m →
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L 1 = ⊤ →
      ∃ S : Boundary.ControlPhaseTree.Construction.BoundaryControlPhaseTree k m R J L, S.blowupDepth = T.blowupDepth := by
  classical
  induction T with
  | terminal ht =>
      intro _ J L hK hbound
      rw [hK] at ht
      exact ⟨.terminal hbound ((BoundaryAuxiliaryOrder.Construction.smooth_boundary_auxiliary_terminal_iff k J L m hm).mp ht), rfl⟩
  | @refineEtale R _ K ι _ A _ f hf hcover children ih =>
      intro _ J L hK hbound
      have hchildren (i : ι) : ∃ S : Boundary.ControlPhaseTree.Construction.BoundaryControlPhaseTree k m (A i)
          (J.map (f i).toRingHom) (L.map (f i).toRingHom),
          S.blowupDepth = (children i).blowupDepth := by
        let : Algebra.Smooth k (A i) := Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k (f i) (hf i)
        have hK' : K.map (f i).toRingHom =
            Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal (J.map (f i).toRingHom) (L.map (f i).toRingHom) m := by
          rw [hK, Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal, Ideal.map_sup, Ideal.map_pow]
          rfl
        have hb' : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (L.map (f i).toRingHom) 1 = ⊤ := by
          rw [← DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k (f i) (hf i) L 1, hbound, Ideal.map_top]
        exact ih i _ _ hK' hb'
      refine ⟨.refineEtale hbound ι A f hf hcover (fun i => (hchildren i).choose), ?_⟩
      change (Finset.univ.sup fun i => (hchildren i).choose.blowupDepth) =
        (Finset.univ.sup fun i => (children i).blowupDepth)
      exact Finset.sup_congr rfl (fun i _ => (hchildren i).choose_spec)
  | @blowup R _ K I _ hperm hsmooth hblowup ι _ _ g D hD hgen children ih =>
      intro _ J L hK hbound
      let : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
      have haux : Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m ≤ I ^ m := hK ▸ hperm
      obtain ⟨hJ, hL⟩ := (BoundaryAuxiliaryOrder.Construction.smooth_generated_boundary_auxiliary_center_iff k I g D hD hgen J L m hm).mp haux
      let : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := hblowup
      have hchildren (i : ι) : ∃ S : Boundary.ControlPhaseTree.Construction.BoundaryControlPhaseTree k m (.of (Blowup.Charts.Construction.blowupChart I (g i)))
          (ControlledTransform.Construction.blowupControlledTransform I J m (g i)) (ControlledTransform.Construction.blowupControlledTransform I L 1 (g i)),
          S.blowupDepth = (children i).blowupDepth := by
        let : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I (g i)) := BlowupChart.Construction.blowupChart_smooth_of_blowup_smooth k I (g i)
        have hK' : ControlledTransform.Construction.blowupControlledTransform I K m (g i) =
            Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal (ControlledTransform.Construction.blowupControlledTransform I J m (g i))
              (ControlledTransform.Construction.blowupControlledTransform I L 1 (g i)) m := by
          rw [hK]
          exact Boundary.AuxiliaryIdeal.Construction.blowup_boundaryAuxiliary_controlledTransform I J L (g i) m hJ hL
        have hb' := Relative.MaximumOrderTransform.Construction.blowup_preserves_relative_differential_order_bound k I L (g i) 1
          (by simpa only [pow_one] using hL) hbound
        exact ih i _ _ hK' hb'
      refine ⟨.blowup hbound I hJ hL
        (fun a => Boundary.AuxiliaryIdeal.Construction.blowup_boundaryAuxiliary_controlledTransform I J L a m hJ hL)
        hsmooth hblowup ι g D hD hgen (fun i => (hchildren i).choose), ?_⟩
      change (Finset.univ.sup fun i => (hchildren i).choose.blowupDepth) + 1 =
        (Finset.univ.sup fun i => (children i).blowupDepth) + 1
      congr 1
      exact Finset.sup_congr rfl (fun i _ => (hchildren i).choose_spec)

/-- Every order-one boundary ideal on a smooth affine surface has a
finite clearance phase at every positive marked control, with no bound
assumed on the original ideal. -/
theorem exists_smooth_surface_boundary_control_phase
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    (hd : ringKrullDim R ≤ 2) (J L : Ideal R) (m : ℕ) (hm : 0 < m)
    (hL : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L 1 = ⊤) :
    Nonempty (Boundary.ControlPhaseTree.Construction.BoundaryControlPhaseTree k m R J L) := by
  have haux := BoundaryAuxiliaryOrder.Construction.smooth_boundary_auxiliary_differential_bound k J L m hm hL
  have htree : Nonempty (AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k m R (Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m)) := by
    have h := SurfaceOrderTree.Construction.exists_smooth_surface_order_reduction_tree k R hd (Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m) (m - 1)
      (by simpa only [Nat.sub_add_cancel hm] using haux)
    simpa only [Nat.sub_add_cancel hm] using h
  obtain ⟨T⟩ := htree
  obtain ⟨S, _⟩ := exists_boundary_control_phase_of_tree k m hm T J L rfl hL
  exact ⟨S⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceBoundaryPhase.Construction
