import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions

/-! # Restriction Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility

noncomputable section

/-! Restricting frame coordinates preserves their transition compatibility, so the compatible section modules have actual restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameTupleRestriction_preserves {V W : X.Opens} (h : W ≤ V)
    (x : SectionModules.OpenFrameLocalTuple U V) (hx : x ∈ SectionModules.openFrameSectionModule U D V) :
    TupleRestrictions.openFrameTupleRestriction U h x ∈ SectionModules.openFrameSectionModule U D W := by
  apply (SectionModules.openFrameSectionModule_mem_iff U D W _).mpr
  intro i j
  let Q := (V ⊓ U i) ⊓ U j
  let Z := (W ⊓ U i) ⊓ U j
  have a : Z ≤ Q := inf_le_inf (inf_le_inf h (le_refl (U i))) (le_refl (U j))
  have qj : Q ≤ V ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have zj : Z ≤ W ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hi := (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U i)))
    (show Z ≤ W ⊓ U i from inf_le_left) (x i)).trans
      (Relative.OpenFunctionUnits.openFunction_restriction_comp (show Q ≤ V ⊓ U i from inf_le_left) a (x i)).symm
  have hj := (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U j))) zj (x j)).trans
    (Relative.OpenFunctionUnits.openFunction_restriction_comp qj a (x j)).symm
  have hc := (SectionModules.openFrameSectionModule_mem_iff U D V x).mp hx i j
  have he := congrArg (fun z : Γ(X, Q) => X.presheaf.map (homOfLE a).op z) hc
  have ht := D.restrict Q Z a i j (inf_le_left.trans inf_le_right) inf_le_right
  exact hi.trans (he.trans (((X.presheaf.map (homOfLE a).op).hom.map_mul _ _).trans
    (congrArg₂ (fun r s : Γ(X, Z) => r * s) ht hj.symm)))

def openFrameSectionRestriction {V W : X.Opens} (h : W ≤ V) :
    SectionModules.openFrameSectionModule U D V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] SectionModules.openFrameSectionModule U D W :=
  ((TupleRestrictions.openFrameTupleRestriction U h).comp (SectionModules.openFrameSectionModule U D V).subtype).codRestrict
    (SectionModules.openFrameSectionModule U D W) (fun x => openFrameTupleRestriction_preserves D h x.val x.property)

theorem openFrameSectionRestriction_refl (V : X.Opens) (x : SectionModules.openFrameSectionModule U D V) :
    openFrameSectionRestriction D (le_refl V) x = x :=
  Subtype.ext (TupleRestrictions.openFrameTupleRestriction_refl U V x.val)

theorem openFrameSectionRestriction_comp {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W)
    (x : SectionModules.openFrameSectionModule U D V) :
    openFrameSectionRestriction D k (openFrameSectionRestriction D h x) =
      openFrameSectionRestriction D (k.trans h) x :=
  Subtype.ext (TupleRestrictions.openFrameTupleRestriction_comp U h k x.val)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility
