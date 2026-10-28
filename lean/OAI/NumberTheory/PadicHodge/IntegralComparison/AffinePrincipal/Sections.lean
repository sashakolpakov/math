import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization
import Mathlib.RingTheory.Localization.BaseChange

/-! # Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

noncomputable section

/-! Quasicoherent sections on an actual principal subopen are the
canonical scalar extension, including the original evaluation map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))

abbrev openSubset := X.basicOpen r
abbrev inclusion : openSubset U r ⟶ U := homOfLE (X.basicOpen_le r)

local instance sectionModule (M : X.Modules) :
    Module Γ(X, U) Γ(M, openSubset U r) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, openSubset U r))

local instance sectionTower (M : X.Modules) :
    IsScalarTower Γ(X, U) Γ(X, openSubset U r) Γ(M, openSubset U r) where
  smul_assoc a b m := by
    change (algebraMap Γ(X, U) Γ(X, openSubset U r) a * b) • m =
      algebraMap Γ(X, U) Γ(X, openSubset U r) a • (b • m)
    exact mul_smul _ _ _

def restriction (M : X.Modules) : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, openSubset U r) where
  toFun := M.presheaf.map (inclusion U r).op
  map_add' := map_add _
  map_smul' a m := M.map_smul (inclusion U r) a m

include hU in
theorem isBaseChange (M : X.Modules) [M.IsQuasicoherent] :
    IsBaseChange Γ(X, openSubset U r) (restriction U r M) := by
  let : IsLocalization.Away r Γ(X, openSubset U r) := hU.isLocalization_basicOpen r
  let : IsLocalizedModule.Away r (restriction U r M) :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize M ⟨U, hU⟩ r
  exact IsLocalizedModule.isBaseChange (Submonoid.powers r) Γ(X, openSubset U r) _

def iso (M : X.Modules) [M.IsQuasicoherent] :
    Γ(X, openSubset U r) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, openSubset U r)] Γ(M, openSubset U r) :=
  (Sections.isBaseChange U hU r M).equiv

@[simp]
theorem iso_tmul (M : X.Modules) [M.IsQuasicoherent]
    (a : Γ(X, openSubset U r)) (m : Γ(M, U)) :
    iso U hU r M (a ⊗ₜ[Γ(X, U)] m) = a • M.presheaf.map (inclusion U r).op m := rfl

theorem iso_tmul_one (M : X.Modules) [M.IsQuasicoherent] (m : Γ(M, U)) :
    iso U hU r M (1 ⊗ₜ[Γ(X, U)] m) = M.presheaf.map (inclusion U r).op m := by
  rw [iso_tmul, one_smul]

theorem naturality {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (x : Γ(X, openSubset U r) ⊗[Γ(X, U)] Γ(M, U)) :
    iso U hU r N ((f.val.app (op U)).hom.baseChange Γ(X, openSubset U r) x) =
      f.val.app (op (openSubset U r)) (iso U hU r M x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, iso_tmul, iso_tmul, map_smul]
    exact congrArg (fun z => a • z)
      (PresheafOfModules.naturality_apply f.val (inclusion U r).op m).symm

theorem evaluation_restriction (M N : X.Modules)
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) (m : Γ(M, U)) :
    Affine.HomEvaluation.evaluation M N (openSubset U r)
        ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).presheaf.map (inclusion U r).op q)
        (M.presheaf.map (inclusion U r).op m) =
      N.presheaf.map (inclusion U r).op (Affine.HomEvaluation.evaluation M N U q m) :=
  Affine.HomEvaluation.restriction M N U (inclusion U r) q m

theorem evaluation_iso_tmul (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).IsQuasicoherent]
    (a b : Γ(X, openSubset U r))
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) (m : Γ(M, U)) :
    Affine.HomEvaluation.evaluation M N (openSubset U r)
        (iso U hU r (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N) (a ⊗ₜ[Γ(X, U)] q))
        (iso U hU r M (b ⊗ₜ[Γ(X, U)] m)) =
      iso U hU r N ((a * b) ⊗ₜ[Γ(X, U)] Affine.HomEvaluation.evaluation M N U q m) := by
  simp only [iso_tmul, map_smul, LinearMap.smul_apply]
  rw [evaluation_restriction, mul_smul]
  exact smul_comm _ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections
