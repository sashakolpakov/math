import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DisjointCenterSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents

/-! # Intrinsic Center Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IntrinsicCenterSequence.Construction

noncomputable section

/-! A smooth intrinsic order center with finitely many components admits a sequence using only integral centers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_integral_center_sequence_of_smooth_intrinsic_center
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥) (n : ℕ)
    [Smooth ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).subschemeι ≫ f)]
    [NoetherianSpace (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).subscheme] :
    ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J, T.integralCenters := by
  let I := Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n
  have hI : I ≠ ⊥ := by
    intro h
    have hle := Global.DifferentialFiltration.Construction.smoothDifferentialIdealSheaf_monotone_order f J (Nat.zero_le n)
    rw [Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_zero] at hle
    exact hJ (le_bot_iff.mp (h ▸ hle))
  let : Fintype (irreducibleComponents I.subscheme) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentFintype I
  let e := (Fintype.equivFin (irreducibleComponents I.subscheme)).symm
  let K (i : Fin (Fintype.card (irreducibleComponents I.subscheme))) := Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I (e i)
  have hp : J ≤ I ^ (n + 1) := (Global.SmoothCenterCriterion.Construction.smooth_global_center_order_iff_differentialIdeal f I J n).mpr le_rfl
  have hprod : (∏ i, K i) = I := by
    change (∏ i, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I (e i)) = I
    rw [e.prod_comp, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_prod]
  exact Finite.DisjointCenterSequence.Construction.exists_finite_disjoint_integral_center_sequence _ X f J n K
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_ne_bot f I hI (e i))
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_integral f I (e i))
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_smooth f I (e i))
    (fun i j hij => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_sup f I (e i) (e j) (fun h => hij (e.injective h)))
    (fun i => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_permissible f I J (n + 1) hp (e i)) hprod.le

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IntrinsicCenterSequence.Construction
