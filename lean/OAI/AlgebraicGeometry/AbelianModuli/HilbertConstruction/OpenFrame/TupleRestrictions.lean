import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionModules
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits

/-! # Tuple Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions

noncomputable section

/-! Coordinate tuples restrict semilinearly along inclusions of opens, with the actual restriction homomorphism on coefficient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

def openFrameTupleRestriction {V W : X.Opens} (h : W ≤ V) :
    SectionModules.OpenFrameLocalTuple U V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] SectionModules.OpenFrameLocalTuple U W where
  toFun s i := X.presheaf.map (homOfLE (inf_le_inf h (le_refl (U i)))).op (s i)
  map_add' s t := funext (fun i => (X.presheaf.map (homOfLE (inf_le_inf h (le_refl (U i)))).op).hom.map_add (s i) (t i))
  map_smul' r s := by
    funext i
    let a : W ⊓ U i ≤ V ⊓ U i := inf_le_inf h (le_refl (U i))
    change X.presheaf.map (homOfLE a).op
        (@Mul.mul Γ(X, V ⊓ U i) inferInstance
          (X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r) (s i)) =
      @Mul.mul Γ(X, W ⊓ U i) inferInstance
        (X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op
          (X.presheaf.map (homOfLE h).op r))
        (X.presheaf.map (homOfLE a).op (s i))
    have hc := (Relative.OpenFunctionUnits.openFunction_restriction_comp (show V ⊓ U i ≤ V from inf_le_left) a r).trans
      (Relative.OpenFunctionUnits.openFunction_restriction_comp h (show W ⊓ U i ≤ W from inf_le_left) r).symm
    exact ((X.presheaf.map (homOfLE a).op).hom.map_mul _ _).trans
      (congrArg (fun z : Γ(X, W ⊓ U i) => z * (X.presheaf.map (homOfLE a).op (s i))) hc)

theorem openFrameTupleRestriction_refl (V : X.Opens) (s : SectionModules.OpenFrameLocalTuple U V) :
    openFrameTupleRestriction U (le_refl V) s = s := by
  funext i
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (.op (V ⊓ U i))) (s i)

theorem openFrameTupleRestriction_comp {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W)
    (s : SectionModules.OpenFrameLocalTuple U V) :
    openFrameTupleRestriction U k (openFrameTupleRestriction U h s) =
      openFrameTupleRestriction U (k.trans h) s := by
  funext i
  exact Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U i))) (inf_le_inf k (le_refl (U i))) (s i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions
