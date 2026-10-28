import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackTuples
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackOnInverseImages

/-! # Pullback Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackCompatibility

noncomputable section

/-! Structural pullback of actual frame coordinates preserves their regular-function transition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : Transitions.OpenFrameTransitions U) (f : X ⟶ Y)

theorem openFramePullbackTuple_compatible (W : Y.Opens) (x : SectionModules.OpenFrameLocalTuple U W)
    (hx : x ∈ SectionModules.openFrameSectionModule U D W) :
    PullbackTuples.openFramePullbackTuple U f W x ∈
      SectionModules.openFrameSectionModule (fun i => f ⁻¹ᵁ U i) (D.pullback f) (f ⁻¹ᵁ W) := by
  apply (SectionModules.openFrameSectionModule_mem_iff _ _ _ _).mpr
  intro i j
  let Q := (W ⊓ U i) ⊓ U j
  have qi : Q ≤ U i := inf_le_left.trans inf_le_right
  have qj : Q ≤ U j := inf_le_right
  have qWj : Q ≤ W ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hi := ConcreteCategory.congr_hom
    (f.naturality (homOfLE (show Q ≤ W ⊓ U i from inf_le_left)).op) (x i)
  have hj := ConcreteCategory.congr_hom (f.naturality (homOfLE qWj).op) (x j)
  have ht := D.pullback_value_on_preimage f Q i j qi qj
  have he := congrArg (f.app Q) ((SectionModules.openFrameSectionModule_mem_iff U D W x).mp hx i j)
  have hm := ((f.app Q).hom.map_mul _ _).trans
    (congrArg₂ (fun a b : Γ(X, f ⁻¹ᵁ Q) => a * b) ht.symm hj)
  exact hi.symm.trans (he.trans hm)

def openFrameSectionPullback (W : Y.Opens) :
    SectionModules.openFrameSectionModule U D W →ₛₗ[(f.app W).hom]
      SectionModules.openFrameSectionModule (fun i => f ⁻¹ᵁ U i) (D.pullback f) (f ⁻¹ᵁ W) :=
  ((PullbackTuples.openFramePullbackTuple U f W).comp (SectionModules.openFrameSectionModule U D W).subtype).codRestrict _
    (fun x => openFramePullbackTuple_compatible D f W x.val x.property)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackCompatibility
