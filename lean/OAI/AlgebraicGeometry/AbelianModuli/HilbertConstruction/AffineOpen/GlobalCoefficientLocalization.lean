import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.RingModulePresheaf

/-! # Global Coefficient Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.GlobalCoefficientLocalization

noncomputable section

/-! Localization on an affine source open retains the action of the
global functions of the entire scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem affineOpen_globalCoefficientSection_isLocalized
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (r : Γ(X, ⊤)) :
    IsLocalizedModule.Away r
      ((Global.RingModulePresheaf.globalRingModulePresheaf M).map
        (homOfLE (X.basicOpen_le (X.presheaf.map U.1.leTop.op r))).op).hom := by
  let s : Γ(X, U.1) := X.presheaf.map U.1.leTop.op r
  let V := X.basicOpen s
  let : Algebra Γ(X, ⊤) Γ(X, U.1) := (X.presheaf.map U.1.leTop.op).hom.toAlgebra
  let : Module Γ(X, ⊤) Γ(M, U.1) :=
    Module.compHom Γ(M, U.1) (X.presheaf.map U.1.leTop.op).hom
  let : Module Γ(X, ⊤) Γ(M, V) :=
    Module.compHom Γ(M, V) (X.presheaf.map V.leTop.op).hom
  let : Module Γ(X, U.1) Γ(M, V) :=
    Module.compHom Γ(M, V) (algebraMap Γ(X, U.1) Γ(X, V))
  let : IsScalarTower Γ(X, ⊤) Γ(X, U.1) Γ(M, U.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Γ(X, ⊤) Γ(X, U.1) Γ(M, V) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a x
    change X.presheaf.map (homOfLE (X.basicOpen_le s)).op
      (X.presheaf.map U.1.leTop.op a) • x =
      X.presheaf.map V.leTop.op a • x
    rw [← X.presheaf.map_comp_apply]
    rfl
  let q : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, V) := {
    toFun := M.presheaf.map (homOfLE (X.basicOpen_le s)).op
    map_add' := (M.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.map_add
    map_smul' := fun a x => M.map_smul (homOfLE (X.basicOpen_le s)) a x }
  have : IsLocalizedModule.Away s q :=
    QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize M U s
  exact IsLocalizedModule.restrictScalars_powers r q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.GlobalCoefficientLocalization
