import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSectionRanges

/-! # Section Endomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SectionEndomorphisms

noncomputable section

/-! Taking sections on an open sends sheaf endomorphisms to actual linear endomorphisms and preserves the endomorphism ring operations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

def moduleSheafSectionEndRingHom : End M →+* Module.End Γ(X, U) Γ(M, U) where
  toFun p := IdempotentSheafSectionRanges.moduleSheafSectionLinearMap p U
  map_one' := by ext x; rfl
  map_mul' p q := by ext x; rfl
  map_zero' := by ext x; rfl
  map_add' p q := by ext x; rfl

theorem moduleSheafSectionEndRingHom_apply (p : End M) (s : Γ(M, U)) :
    moduleSheafSectionEndRingHom M U p s = p.app U s := rfl

theorem moduleSheafSum_app {I : Type v} [Fintype I] (p : I → End M) (s : Γ(M, U)) :
    (∑ i : I, p i).app U s = ∑ i : I, (p i).app U s := by
  have h := congrArg (fun f : Module.End Γ(X, U) Γ(M, U) => f s)
    (map_sum (moduleSheafSectionEndRingHom M U) p Finset.univ)
  simpa only [LinearMap.sum_apply, moduleSheafSectionEndRingHom_apply] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SectionEndomorphisms
