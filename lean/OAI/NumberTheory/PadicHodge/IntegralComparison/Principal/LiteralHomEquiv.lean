import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LiteralHomEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Literal Hom Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.LiteralHomEquiv

noncomputable section

/-! On a principal affine subopen the original sheaf Hom is the Hom
from the original ambient affine section module to the restricted target.
The normalization is literal restriction followed by evaluation. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))

local instance sectionModule (M : X.Modules) : Module Γ(X, U) Γ(M, AffinePrincipal.Sections.openSubset U r) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, AffinePrincipal.Sections.openSubset U r))
local instance sectionTower (M : X.Modules) :
    IsScalarTower Γ(X, U) Γ(X, AffinePrincipal.Sections.openSubset U r) Γ(M, AffinePrincipal.Sections.openSubset U r) where
  smul_assoc a b m := by
    change (algebraMap Γ(X, U) Γ(X, AffinePrincipal.Sections.openSubset U r) a * b) • m =
      algebraMap Γ(X, U) Γ(X, AffinePrincipal.Sections.openSubset U r) a • (b • m)
    exact mul_smul _ _ _

variable (M N : X.Modules) [M.IsQuasicoherent]

def equiv : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, AffinePrincipal.Sections.openSubset U r) ≃ₗ[Γ(X, U)]
    (Γ(M, U) →ₗ[Γ(X, U)] Γ(N, AffinePrincipal.Sections.openSubset U r)) :=
  ((Affine.LiteralHomEquiv.equiv (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) M N).trans
    ((LinearEquiv.arrowCongr (AffinePrincipal.Sections.iso U hU r M).symm
        (LinearEquiv.refl Γ(X, AffinePrincipal.Sections.openSubset U r) Γ(N, AffinePrincipal.Sections.openSubset U r))).trans
      (LinearMap.liftBaseChangeEquiv Γ(X, AffinePrincipal.Sections.openSubset U r)).symm)).restrictScalars Γ(X, U)

theorem equiv_apply (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, AffinePrincipal.Sections.openSubset U r)) (m : Γ(M, U)) :
    equiv U hU r M N q m =
      Affine.HomEvaluation.evaluation M N (AffinePrincipal.Sections.openSubset U r) q (M.presheaf.map (AffinePrincipal.Sections.inclusion U r).op m) := by
  change Affine.HomEvaluation.evaluation M N (AffinePrincipal.Sections.openSubset U r) q
    (AffinePrincipal.Sections.iso U hU r M (1 ⊗ₜ[Γ(X, U)] m)) = _
  rw [AffinePrincipal.Sections.iso_tmul_one]

theorem precomp {M' : X.Modules} [M'.IsQuasicoherent] (f : M ⟶ M')
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M' N, AffinePrincipal.Sections.openSubset U r)) (m : Γ(M, U)) :
    equiv U hU r M N ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap f (𝟙 N)).val.app (op (AffinePrincipal.Sections.openSubset U r)) q) m =
      equiv U hU r M' N q (f.val.app (op U) m) := by
  rw [equiv_apply, equiv_apply]
  change Affine.HomEvaluation.evaluation M' N (AffinePrincipal.Sections.openSubset U r) q
    (f.val.app (op (AffinePrincipal.Sections.openSubset U r)) (M.presheaf.map (AffinePrincipal.Sections.inclusion U r).op m)) = _
  exact congrArg (Affine.HomEvaluation.evaluation M' N (AffinePrincipal.Sections.openSubset U r) q)
    (PresheafOfModules.naturality_apply f.val (AffinePrincipal.Sections.inclusion U r).op m)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.LiteralHomEquiv
