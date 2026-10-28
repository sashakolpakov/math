import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSummands
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Idempotent Sheaf Section Ranges -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSectionRanges

noncomputable section

/-! Sections of the constructed idempotent sheaf summand are exactly the range of the actual section projector, over every open subset. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {M : X.Modules}

def moduleSheafSectionLinearMap {L N : X.Modules} (f : L ⟶ N) (U : X.Opens) :
    Γ(L, U) →ₗ[Γ(X, U)] Γ(N, U) := (f.val.app (.op U)).hom

def idempotentSheafSectionRangeEquiv (p : End M) (hp : p ≫ p = p) (U : X.Opens) :
    Γ(IdempotentSheafSummands.idempotentSheafSummand p, U) ≃ₗ[Γ(X, U)] (moduleSheafSectionLinearMap p U).range where
  toFun x := ⟨(IdempotentSheafSummands.idempotentSheafInclusion p).app U x, ⟨(IdempotentSheafSummands.idempotentSheafInclusion p).app U x,
    ConcreteCategory.congr_hom
      (congrArg (fun f : IdempotentSheafSummands.idempotentSheafSummand p ⟶ M => f.app U) (IdempotentSheafSummands.idempotentSheafInclusion_fixed p)) x⟩⟩
  invFun x := (IdempotentSheafSummands.idempotentSheafRetraction p hp).app U x.val
  left_inv x := ConcreteCategory.congr_hom
    (congrArg (fun f : End (IdempotentSheafSummands.idempotentSheafSummand p) => f.app U)
      (IdempotentSheafSummands.idempotentSheafInclusion_retraction p hp)) x
  right_inv x := by
    apply Subtype.ext
    have hr := ConcreteCategory.congr_hom (congrArg (fun f : End M => f.app U)
      (IdempotentSheafSummands.idempotentSheafRetraction_inclusion p hp)) x.val
    have hi := ConcreteCategory.congr_hom (congrArg (fun f : End M => f.app U) hp)
    obtain ⟨y, hy⟩ := x.property
    exact hr.trans ((congrArg (fun z => p.app U z) hy.symm).trans ((hi y).trans hy))
  map_add' x y := Subtype.ext ((moduleSheafSectionLinearMap (IdempotentSheafSummands.idempotentSheafInclusion p) U).map_add x y)
  map_smul' r x := Subtype.ext ((moduleSheafSectionLinearMap (IdempotentSheafSummands.idempotentSheafInclusion p) U).map_smul r x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSectionRanges
