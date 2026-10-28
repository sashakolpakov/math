import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalFreeness

/-! # Global Tuples -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalTuples

noncomputable section

/-! Global frame-coordinate tuples identify with regular functions on the covering opens, over the ring of global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

abbrev OpenFrameGlobalTuple := (i : ι) → Relative.OpenFunctionModules.relativeOpenFunctionModule (⊤ : X.Opens) (U i) le_top

def openFrameGlobalTupleEquiv : SectionModules.OpenFrameLocalTuple U ⊤ ≃ₗ[Γ(X, ⊤)] OpenFrameGlobalTuple U :=
  LinearEquiv.piCongrRight (fun i => LinearEquiv.ofBijective
    (Relative.OpenFunctionModules.relativeOpenFunctionRestriction (⊤ : X.Opens) inf_le_left le_top
      (le_inf le_top (le_refl (U i)))).hom
    (LocalFreeness.openFunctionRestriction_bijective_of_eq (le_inf le_top (le_refl (U i)))
      (by ext x; simp)))

theorem openFrameGlobalTupleEquiv_apply (x : SectionModules.OpenFrameLocalTuple U ⊤) (i : ι) :
    openFrameGlobalTupleEquiv U x i =
      X.presheaf.map (homOfLE (show U i ≤ ⊤ ⊓ U i from le_inf le_top le_rfl)).op (x i) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalTuples
