import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PowerScaling
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CompanionOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback

/-! # Companion Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionIdeal.Construction

noncomputable section

/-! Native global companion ideals retain both residual and exceptional controls. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def globalMarkedIntersection {X : Scheme.{u}} (J L : X.IdealSheafData) (b c : ℕ) : X.IdealSheafData :=
  J ^ c ⊔ L ^ b

def globalCompanionIdeal {X : Scheme.{u}} (J M : X.IdealSheafData) (m b : ℕ) : X.IdealSheafData :=
  globalMarkedIntersection J M m (b - m)

theorem globalMarkedIntersection_ideal {X : Scheme.{u}} (J L : X.IdealSheafData)
    (b c : ℕ) (U : X.affineOpens) :
    (globalMarkedIntersection J L b c).ideal U = MarkedIdealIntersection.Construction.markedIdealIntersection (J.ideal U) (L.ideal U) b c := rfl

theorem globalCompanionIdeal_ideal {X : Scheme.{u}} (J M : X.IdealSheafData)
    (m b : ℕ) (U : X.affineOpens) :
    (globalCompanionIdeal J M m b).ideal U = CompanionCenter.Construction.companionIdeal (J.ideal U) (M.ideal U) m b := rfl

theorem globalMarkedIntersection_comap {Y X : Scheme.{u}} (J L : X.IdealSheafData)
    (b c : ℕ) (π : Y ⟶ X) :
    (globalMarkedIntersection J L b c).comap π = globalMarkedIntersection (J.comap π) (L.comap π) b c := by
  rw [globalMarkedIntersection, Scheme.IdealSheafData.comap_sup, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow]
  rfl

theorem globalCompanionIdeal_comap {Y X : Scheme.{u}} (J M : X.IdealSheafData)
    (m b : ℕ) (π : Y ⟶ X) :
    (globalCompanionIdeal J M m b).comap π = globalCompanionIdeal (J.comap π) (M.comap π) m b :=
  globalMarkedIntersection_comap J M m (b - m) π

theorem globalMarkedIntersection_permissible {X : Scheme.{u}}
    (I J L : X.IdealSheafData) (b c : ℕ) (hJ : J ≤ I ^ b) (hL : L ≤ I ^ c) :
    globalMarkedIntersection J L b c ≤ I ^ (b * c) := by
  intro U
  exact MarkedIdealIntersection.Construction.markedIdealIntersection_permissible (I.ideal U) (J.ideal U) (L.ideal U) b c (hJ U) (hL U)

theorem globalMarkedIntersection_smooth_center_iff {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J L : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)]
    (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    globalMarkedIntersection J L b c ≤ I ^ (b * c) ↔ J ≤ I ^ b ∧ L ≤ I ^ c := by
  constructor
  · intro h
    have hJ : J ^ c ≤ I ^ (b * c) := le_sup_left.trans h
    have hL : L ^ b ≤ I ^ (c * b) := by
      rw [Nat.mul_comm c b]
      exact le_sup_right.trans h
    exact ⟨PowerScaling.Construction.smooth_global_center_ideal_power_root f I J b c hc hJ,
      PowerScaling.Construction.smooth_global_center_ideal_power_root f I L c b hb hL⟩
  · rintro ⟨hJ, hL⟩
    exact globalMarkedIntersection_permissible I J L b c hJ hL

theorem globalCompanionIdeal_smooth_center_permissible {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J M : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (m b : ℕ) (hm : 0 < m) (hmb : m < b)
    (hc : globalCompanionIdeal J M m b ≤ I ^ (m * (b - m))) :
    J ≤ I ^ m ∧ M ≤ I ^ (b - m) ∧ M * J ≤ I ^ b := by
  obtain ⟨hJ, hM⟩ := (globalMarkedIntersection_smooth_center_iff f I J M m (b - m) hm (by omega)).mp hc
  refine ⟨hJ, hM, ?_⟩
  intro U
  exact ResidualCoefficientTransform.Construction.product_center_permissible (I.ideal U) (M.ideal U) (J.ideal U) (b - m) m b (by omega) (hM U) (hJ U)

theorem globalCompanionIdeal_differential_bound {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J M : X.IdealSheafData) (m b : ℕ) (hmb : m < b) (hJ : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (globalCompanionIdeal J M m b) (m * (b - m)) = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  have h := congrArg (fun I : X.IdealSheafData => I.ideal U) hJ
  exact Blowups.Smooth.CompanionOrder.Construction.smooth_companion_relative_differential_bound ℂ (J.ideal U) (M.ideal U) m b hmb h

theorem globalCompanionIdeal_terminal_residual_drop {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J M : X.IdealSheafData) (m b : ℕ) (hm : 0 < m) (hmb : m < b)
    (hJ : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤)
    (hc : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (globalCompanionIdeal J M m b) (m * (b - m) - 1) = ⊤) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (M * J) (b - 1) ⊔ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1) = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  have hJ' := congrArg (fun I : X.IdealSheafData => I.ideal U) hJ
  have hc' := congrArg (fun I : X.IdealSheafData => I.ideal U) hc
  exact Blowups.Smooth.CompanionOrder.Construction.smooth_companion_terminal_residual_drop ℂ (J.ideal U) (M.ideal U) m b hm hmb hJ' hc'

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionIdeal.Construction
