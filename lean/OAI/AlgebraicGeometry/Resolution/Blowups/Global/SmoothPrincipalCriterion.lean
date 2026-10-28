import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.PrincipalDifferentialCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalDifferentialSmoothness
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalRegular

/-! # Smooth Principal Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothPrincipalCriterion.Construction

noncomputable section

/-! Smoothness of a nonzero locally principal hypersurface in an integral smooth ambient scheme is equivalent to a unit first differential ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smooth_locallyPrincipal_firstDifferential_top
    {X : Scheme} [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (H : X.IdealSheafData) (hH : H ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H)
    [Smooth (H.subschemeι ≫ f)] : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f H 1 = ⊤ := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let D := Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f H 1
  apply (Scheme.IdealSheafData.support_eq_bot_iff D).mp
  apply SetLike.coe_injective
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨U, hxU, z, hz, hHz⟩ := Locally.PrincipalRegular.Construction.locallyPrincipal_regular_generators H hH hlocal x
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let : Algebra.Smooth ℂ (Γ(X, U) ⧸ Ideal.span {z}) := by
    rw [← hHz]
    exact SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f H U
  have htop : D.ideal U = ⊤ := by
    change Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal ℂ (H.ideal U) = ⊤
    rw [hHz]
    exact Blowups.Smooth.PrincipalDifferentialCriterion.Construction.firstDifferential_principal_top_of_smooth_quotient ℂ z hz
  have hm := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := D) hxU).mp hx
  rw [htop] at hm
  change x ∈ X.zeroLocus (Set.univ : Set Γ(X, U)) at hm
  rw [Scheme.zeroLocus_univ] at hm
  exact hm hxU

theorem locallyPrincipal_subscheme_smooth_iff_firstDifferential_top
    {X : Scheme} [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (H : X.IdealSheafData) (hH : H ≠ ⊥) (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) :
    Smooth (H.subschemeι ≫ f) ↔ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f H 1 = ⊤ := by
  constructor
  · intro hs
    let : Smooth (H.subschemeι ≫ f) := hs
    exact smooth_locallyPrincipal_firstDifferential_top f H hH hlocal
  · exact PrincipalDifferentialSmoothness.Construction.locallyPrincipal_subscheme_smooth_of_firstDifferential_top f H hlocal

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothPrincipalCriterion.Construction
