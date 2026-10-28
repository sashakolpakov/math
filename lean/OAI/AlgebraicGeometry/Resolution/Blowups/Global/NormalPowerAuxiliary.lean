import OAI.AlgebraicGeometry.Resolution.Blowups.NormalPowerDifferentialIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HypersurfaceNormalCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CarrierAuxiliaryCoefficients
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothPrincipalCriterion

/-! # Normal Power Auxiliary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalPowerAuxiliary.Construction

noncomputable section

/-! A smooth Cartier carrier is actual maximal contact for its boundary auxiliary ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smooth_normal_power_differential_ideal
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (H : X.IdealSheafData) (hH : H ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) [Smooth (H.subschemeι ≫ f)] (n : ℕ) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (H ^ (n + 1)) n = H := by
  classical
  choose U hxU hcase using fun x : X => HypersurfaceNormalCover.Construction.exists_global_hypersurface_normal_neighborhood f H H hH hlocal le_rfl x
  have hcover : (⨆ x, (U x).val) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro x
  let : Algebra ℂ Γ(X, U x) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (U x)
  let : Algebra ℚ Γ(X, U x) := ((algebraMap ℂ Γ(X, U x)).comp (algebraMap ℚ ℂ)).toAlgebra
  change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ ((H.ideal (U x)) ^ (n + 1)) n = H.ideal (U x)
  rcases hcase x with hunit | hframe
  · rw [hunit, Ideal.top_pow]
    exact top_le_iff.mp (Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order ℂ (⊤ : Ideal Γ(X, U x)) (Nat.zero_le n))
  · obtain ⟨ι, hdec, g, D, hD, _, i, hH⟩ := hframe
    rw [hH]
    exact NormalPowerDifferentialIdeal.Construction.normal_power_differential_ideal ℂ (D i) (g i).val (by rw [hD, ite_eq_left rfl]) n

theorem smooth_carrier_le_auxiliary_tangent
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hH : H ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) [Smooth (H.subschemeι ≫ f)] (n : ℕ) :
    H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H (n + 1)) n := by
  exact (smooth_normal_power_differential_ideal f H hH hlocal n).symm.le.trans
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_mono f (le_sup_right : H ^ (n + 1) ≤ J ⊔ H ^ (n + 1)) n)

theorem smooth_carrier_auxiliary_differential_bound
    {X : Scheme} [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J H : X.IdealSheafData) (hH : H ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H)
    [Smooth (H.subschemeι ≫ f)] (b : ℕ) (hb : 0 < b) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H b) b = ⊤ := by
  have hfirst := SmoothPrincipalCriterion.Construction.smooth_locallyPrincipal_firstDifferential_top f H hH hlocal
  apply Scheme.IdealSheafData.ext
  funext U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  have hU : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (H.ideal U) 1 = ⊤ :=
    congrArg (fun I : X.IdealSheafData => I.ideal U) hfirst
  exact Blowups.Smooth.BoundaryAuxiliaryOrder.Construction.smooth_boundary_auxiliary_differential_bound ℂ (J.ideal U) (H.ideal U) b hb hU

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalPowerAuxiliary.Construction
