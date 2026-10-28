import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ColonLocalization
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian Ideal Sheaf Colon -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianIdealSheafColon.Construction

noncomputable section

/-! The ideal quotient as a native ideal sheaf on a locally Noetherian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The coherent ideal quotient, defined by the actual affine colon ideals. -/
def noetherianIdealSheafColon (J K : X.IdealSheafData) : X.IdealSheafData where
  ideal U := (J.ideal U).colon (K.ideal U : Set Γ(X, U))
  map_ideal_basicOpen U s := by
    let V := X.affineBasicOpen s
    have hVU : V ≤ U := X.basicOpen_le s
    let : Algebra Γ(X, U) Γ(X, V) := (Blowup.Functor.Construction.affineRestriction hVU).toAlgebra
    let : IsLocalization.Away s Γ(X, V) :=
      U.2.isLocalization_of_eq_basicOpen s (homOfLE hVU) rfl
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    have hfg : (K.ideal U).FG := IsNoetherian.noetherian _
    have he := Blowups.Ideal.ColonLocalization.Construction.localization_map_colon_fg (S := Γ(X, V)) (Submonoid.powers s) (J.ideal U) (K.ideal U) hfg
    change ((J.ideal U).colon (K.ideal U : Set Γ(X, U))).map (Blowup.Functor.Construction.affineRestriction hVU) = _
    exact he.trans (congrArg₂ (fun A B : Ideal Γ(X, V) => A.colon (B : Set Γ(X, V)))
      (J.map_ideal hVU) (K.map_ideal hVU))

theorem noetherianIdealSheafColon_ideal (J K : X.IdealSheafData) (U : X.affineOpens) :
    (noetherianIdealSheafColon J K).ideal U = (J.ideal U).colon (K.ideal U : Set Γ(X, U)) := rfl

theorem le_noetherianIdealSheafColon (J K : X.IdealSheafData) :
    J ≤ noetherianIdealSheafColon J K := by
  intro U
  exact Ideal.le_colon

/-- If the original ideal sheaf is nonzero, so is its quotient by any
other ideal sheaf. -/
theorem noetherianIdealSheafColon_ne_bot (J K : X.IdealSheafData) (hJ : J ≠ ⊥) :
    noetherianIdealSheafColon J K ≠ ⊥ := by
  intro h
  exact hJ (le_bot_iff.mp (h ▸ le_noetherianIdealSheafColon J K))

theorem noetherianIdealSheafColon_eq_top_iff (J K : X.IdealSheafData) :
    noetherianIdealSheafColon J K = ⊤ ↔ K ≤ J := by
  constructor
  · intro h U
    have he := congrArg (fun I : X.IdealSheafData => I.ideal U) h
    exact (Submodule.colon_eq_top_iff_subset _).mp he
  · intro h
    apply Scheme.IdealSheafData.ext
    funext U
    exact (Submodule.colon_eq_top_iff_subset _).mpr (h U)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianIdealSheafColon.Construction
