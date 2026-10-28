import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Tuple Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleSheaf

noncomputable section

/-! Arbitrary tuples of regular functions on intersections with fixed opens form a sheaf; gluing is performed in each actual section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

def openFrameTuplePresheaf : TopCat.Presheaf (Type u) X where
  obj V := SectionModules.OpenFrameLocalTuple U V.unop
  map h := TypeCat.ofHom (TupleRestrictions.openFrameTupleRestriction U h.unop.le)
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro s
    exact TupleRestrictions.openFrameTupleRestriction_refl U V.unop s
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (TupleRestrictions.openFrameTupleRestriction_comp U h.unop.le k.unop.le s).symm

theorem openFrameTuple_components_compatible {α : Type u} (V : α → X.Opens)
    (s : ∀ a, SectionModules.OpenFrameLocalTuple U (V a))
    (hs : ∀ a b, TupleRestrictions.openFrameTupleRestriction U (show V a ⊓ V b ≤ V a from inf_le_left) (s a) =
      TupleRestrictions.openFrameTupleRestriction U (show V a ⊓ V b ≤ V b from inf_le_right) (s b)) (i : ι) :
    X.presheaf.IsCompatible (fun a => V a ⊓ U i) (fun a => s a i) := by
  intro a b
  let Z := (V a ⊓ U i) ⊓ (V b ⊓ U i)
  have hz : Z ≤ (V a ⊓ V b) ⊓ U i :=
    le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_left.trans inf_le_right)
  have he := congrArg (fun t : SectionModules.OpenFrameLocalTuple U (V a ⊓ V b) => t i) (hs a b)
  have hr := congrArg (fun z : Γ(X, (V a ⊓ V b) ⊓ U i) => X.presheaf.map (homOfLE hz).op z) he
  exact (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf (show V a ⊓ V b ≤ V a from inf_le_left)
    (le_refl (U i))) hz (s a i)).symm.trans
      (hr.trans (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf (show V a ⊓ V b ≤ V b from inf_le_right)
        (le_refl (U i))) hz (s b i)))

theorem openFrameTuplePresheaf_isSheaf : (openFrameTuplePresheaf U).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr
  intro α V s hs
  have hcoord (i : ι) : ∃! t : Γ(X, (iSup V) ⊓ U i), ∀ a,
      X.presheaf.map (homOfLE (inf_le_inf (le_iSup V a) (le_refl (U i)))).op t = s a i := by
    apply X.sheaf.existsUnique_gluing' (fun a => V a ⊓ U i) ((iSup V) ⊓ U i)
      (fun a => homOfLE (inf_le_inf (le_iSup V a) (le_refl (U i))))
    · intro x hx
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx.1
      exact Opens.mem_iSup.mpr ⟨a, ha, hx.2⟩
    · exact openFrameTuple_components_compatible U V s hs i
  choose t ht hu using hcoord
  refine ⟨t, ?_, ?_⟩
  · intro a
    funext i
    exact ht i a
  · intro q hq
    funext i
    exact hu i (q i) (fun a => congrFun (hq a) i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleSheaf
