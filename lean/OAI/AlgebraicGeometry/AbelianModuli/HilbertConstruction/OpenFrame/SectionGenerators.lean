import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionModules
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateCompatibility

/-! # Section Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame

noncomputable section

/-! A frame on a containing chart gives a linear generator of the module of compatible local coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def SectionGenerators.openFrameGenerator (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Γ(X, V) →ₗ[Γ(X, V)] SectionModules.openFrameSectionModule U D V :=
  (LinearMap.pi (fun i =>
    (Relative.OpenFunctionScalars.relativeOpenFunctionScalar V (V ⊓ U i) inf_le_left
      (D.value (V ⊓ U i) i k inf_le_right (inf_le_left.trans hV)).val).hom.comp
        (Relative.OpenFunctionUnits.relativeOpenFunctionUnitMap V (V ⊓ U i) inf_le_left))).codRestrict
    (SectionModules.openFrameSectionModule U D V) (by
      intro x
      apply (SectionModules.openFrameSectionModule_mem_iff U D V _).mpr
      intro i j
      exact D.frameValues_compatible V k hV x i j)

theorem SectionGenerators.openFrameGenerator_apply (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) (i : ι) :
    (SectionGenerators.openFrameGenerator D V k hV x).val i = D.frameValues V k hV x i := rfl

theorem Transitions.OpenFrameTransitions.frameValues_self (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) :
    D.frameValues V k hV x k =
      X.presheaf.map (homOfLE (show V ⊓ U k ≤ V from inf_le_left)).op x := by
  exact (congrArg (fun a : Γ(X, V ⊓ U k)ˣ => a.val *
    X.presheaf.map (homOfLE (show V ⊓ U k ≤ V from inf_le_left)).op x)
      (D.self (V ⊓ U k) k inf_le_right)).trans (one_mul _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame
