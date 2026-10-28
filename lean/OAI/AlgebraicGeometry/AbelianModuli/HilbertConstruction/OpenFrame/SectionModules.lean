import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionScalars

/-! # Section Modules -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionModules

noncomputable section

/-! Compatible regular-function coordinates for a frame cocycle form actual modules over the functions on each open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

abbrev OpenFrameLocalTuple (V : X.Opens) :=
  (i : ι) → Relative.OpenFunctionModules.relativeOpenFunctionModule V (V ⊓ U i) inf_le_left

def openFrameDifference (D : Transitions.OpenFrameTransitions U) (V : X.Opens) (i j : ι) :
    OpenFrameLocalTuple U V →ₗ[Γ(X, V)] Relative.OpenFunctionModules.relativeOpenFunctionModule V ((V ⊓ U i) ⊓ U j)
      (inf_le_left.trans inf_le_left) :=
  (Relative.OpenFunctionModules.relativeOpenFunctionRestriction V inf_le_left (inf_le_left.trans inf_le_left) inf_le_left).hom.comp
      (LinearMap.proj i) -
    (Relative.OpenFunctionScalars.relativeOpenFunctionScalar V ((V ⊓ U i) ⊓ U j) (inf_le_left.trans inf_le_left)
      (D.value ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right).val).hom.comp
        ((Relative.OpenFunctionModules.relativeOpenFunctionRestriction V inf_le_left (inf_le_left.trans inf_le_left)
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).hom.comp (LinearMap.proj j))

def openFrameSectionModule (D : Transitions.OpenFrameTransitions U) (V : X.Opens) : Submodule Γ(X, V) (OpenFrameLocalTuple U V) :=
  ⨅ i, ⨅ j, (openFrameDifference U D V i j).ker

theorem openFrameSectionModule_mem_iff (D : Transitions.OpenFrameTransitions U) (V : X.Opens) (x : OpenFrameLocalTuple U V) :
    x ∈ openFrameSectionModule U D V ↔ ∀ i j,
      X.presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U i from inf_le_left)).op (x i) =
        (D.value ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right).val *
          X.presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U j from
            le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (x j) := by
  simp only [openFrameSectionModule, Submodule.mem_iInf, LinearMap.mem_ker]
  apply forall₂_congr
  intro i j
  exact sub_eq_zero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionModules
