import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafQuotients
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBaseChange
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Annihilator Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AnnihilatorBaseChange

noncomputable section

/-!
# CartierDuality: arbitrary base change of pairings and annihilator subobjects
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v u' v'

namespace Construction.BaseChangeKernels

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasKernels C]
    {C' : Type u'} [Category.{v'} C'] [HasZeroMorphisms C'] [HasKernels C']
    (F : C ⥤ C') [F.PreservesZeroMorphisms] [F.PreservesMonomorphisms]
    [PreservesLimitsOfShape WalkingParallelPair F]

omit [HasKernels C'] in
/-- A functor preserving kernels carries their actual subobjects to
the kernel subobjects of the mapped morphisms. -/
theorem map_kernel {X Y : C} (a : X ⟶ Y) :
    Subobject.mk (F.map (kernelSubobject a).arrow) = kernelSubobject (F.map a) := by
  apply Subobject.mk_eq_mk_of_comm _ _
    (F.mapIso (kernelSubobjectIso a) ≪≫ PreservesKernel.iso F a)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, PreservesKernel.iso_hom,
    kernelComparison_comp_ι, ← F.map_comp, kernelSubobject_arrow]

/-- Natural compatibility with a contravariant character functor
identifies the mapped annihilator as the annihilator of the mapped subgroup. -/
theorem annihilator_map (D : Cᵒᵖ ⥤ C) (D' : C'ᵒᵖ ⥤ C')
    (δ : ∀ X : C, F.obj (D.obj (Opposite.op X)) ≅ D'.obj (Opposite.op (F.obj X)))
    (hn : ∀ {X Y : C} (a : X ⟶ Y), F.map (D.map a.op) ≫ (δ X).hom =
      (δ Y).hom ≫ D'.map (F.map a).op)
    {G K : C} (r : K ⟶ D.obj (Opposite.op G)) (H : Subobject G) :
    Subobject.mk (F.map (kernelSubobject (r ≫ D.map H.arrow.op)).arrow) =
      kernelSubobject ((F.map r ≫ (δ G).hom) ≫
        D'.map (Subobject.mk (F.map H.arrow)).arrow.op) := by
  let j := Subobject.underlyingIso (F.map H.arrow)
  let p := (δ (H : C)).hom ≫ D'.map j.hom.op
  let : IsIso p := inferInstanceAs (IsIso ((δ (H : C)).hom ≫ D'.map j.hom.op))
  have hj : j.hom ≫ F.map H.arrow = (Subobject.mk (F.map H.arrow)).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk (F.map H.arrow)
  have hf : (F.map r ≫ (δ G).hom) ≫ D'.map (Subobject.mk (F.map H.arrow)).arrow.op =
      F.map (r ≫ D.map H.arrow.op) ≫ p := by
    rw [← hj, op_comp, D'.map_comp]
    dsimp only [p]
    rw [Category.assoc, ← Category.assoc (δ G).hom, ← hn H.arrow,
      Category.assoc, ← Category.assoc (F.map r), ← F.map_comp]
  exact (map_kernel F (r ≫ D.map H.arrow.op)).trans
    ((kernelSubobject_comp_mono (F.map (r ≫ D.map H.arrow.op)) p).symm.trans
      (congrArg (fun a : F.obj K ⟶ D'.obj (Opposite.op (Subobject.mk (F.map H.arrow) : C')) =>
        kernelSubobject a) hf.symm))

end Construction.BaseChangeKernels

namespace Construction.Schemes

/-- Base change of commutative fppf sheaves preserves limits. -/
instance baseChangeFppfAb_preservesLimits {S T : Scheme.{u}} (f : T ⟶ S) :
    PreservesLimits (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f) := by
  let : PreservesLimits (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f ⋙
      sheafToPresheaf (Scheme.fppfTopology.over T) CommGrpCat.{u + 1}) :=
    preservesLimits_of_natIso
      ((Over.map f).sheafPushforwardContinuousCompSheafToPresheafIso CommGrpCat.{u + 1}
        (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)).symm
  exact preservesLimits_of_reflects_of_preserves (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f)
    (sheafToPresheaf (Scheme.fppfTopology.over T) CommGrpCat.{u + 1})

/-- Base change preserves the concrete trivial sheaf morphisms. -/
instance baseChangeFppfAb_preservesZero {S T : Scheme.{u}} (f : T ⟶ S) :
    (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The Cartier base-change comparison is natural in the source sheaf. -/
theorem sheafDualBaseChangeIso_natural {S T : Scheme.{u}} (f : T ⟶ S)
    {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (a : H ⟶ G) :
    (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map a.op) ≫
        (SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f H).hom =
      (SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f G).hom ≫
        (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor T).map ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map a).op := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over T) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext U
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  apply NatTrans.ext
  funext V
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  rfl

/-- The canonical base-change comparison transports the actual value
of each character through the multiplicative-group base-change map. -/
theorem sheafDualBaseChangeIso_value {S T : Scheme.{u}} (f : T ⟶ S)
    (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (U : Over T)
    (χ : ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G)).obj.obj (Opposite.op U))
    (x : ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj G).obj.obj (Opposite.op U)) :
    SheafEvaluation.Construction.Schemes.sheafCharacterValue ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj G) U
      ((SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f G).hom.hom.app (Opposite.op U) χ) x =
      (SheafBaseChange.Construction.Schemes.multiplicativeFppfAbBaseChangeIso f).hom.hom.app (Opposite.op U)
        (SheafEvaluation.Construction.Schemes.sheafCharacterValue G ((Over.map f).obj U) χ x) := rfl

/-- The actual base change of a subgroup is represented by the
base-changed monomorphism into the base-changed ambient sheaf. -/
def baseChangeSubobject {S T : Scheme.{u}} (f : T ⟶ S) {G : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (H : Subobject G) : Subobject ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj G) :=
  Subobject.mk ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map H.arrow)

/-- Base change of a pairing uses restriction of its character-valued
right adjoint and the canonical Cartier base-change comparison. -/
def baseChangePairing {S T : Scheme.{u}} (f : T ⟶ S) {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) :
    SheafEvaluation.Construction.Schemes.BilinearPairing ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj G) ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj K) :=
  (SheafEvaluation.Construction.Schemes.BilinearPairing.mk ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map e.rightAdjoint ≫
    (SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f G).hom)).flip

/-- The right adjoint of the base-changed pairing is the canonical
base change of the original right adjoint. -/
theorem baseChangePairing_rightAdjoint {S T : Scheme.{u}} (f : T ⟶ S) {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) :
    (baseChangePairing f e).rightAdjoint =
      (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map e.rightAdjoint ≫ (SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f G).hom :=
  congrArg SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint
    (SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip (SheafEvaluation.Construction.Schemes.BilinearPairing.mk ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map e.rightAdjoint ≫
      (SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f G).hom)))

/-- The base-changed pairing evaluates to the base change of the
original pairing on every test scheme. -/
theorem baseChangePairing_value {S T : Scheme.{u}} (f : T ⟶ S) {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) (U : Over T)
    (x : ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj G).obj.obj (Opposite.op U))
    (y : ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj K).obj.obj (Opposite.op U)) :
    SheafEvaluation.Construction.Schemes.sheafCharacterValue ((SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).obj G) U
      ((baseChangePairing f e).rightAdjoint.hom.app (Opposite.op U) y) x =
      (SheafBaseChange.Construction.Schemes.multiplicativeFppfAbBaseChangeIso f).hom.hom.app (Opposite.op U)
        (SheafEvaluation.Construction.Schemes.sheafCharacterValue G ((Over.map f).obj U)
          (e.rightAdjoint.hom.app (Opposite.op ((Over.map f).obj U)) y) x) := by
  rw [baseChangePairing_rightAdjoint]
  exact sheafDualBaseChangeIso_value f G U
    (e.rightAdjoint.hom.app (Opposite.op ((Over.map f).obj U)) y) x

/-- Taking the annihilator commutes with arbitrary scheme base change,
as an equality of subgroup sheaves in the canonical common ambient sheaf. -/
theorem sheafAnnihilator_baseChange {S T : Scheme.{u}} (f : T ⟶ S)
    {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) (H : Subobject G) :
    baseChangeSubobject f (SheafQuotients.Construction.Schemes.sheafAnnihilator e H) =
      SheafQuotients.Construction.Schemes.sheafAnnihilator (baseChangePairing f e) (baseChangeSubobject f H) := by
  have h := BaseChangeKernels.annihilator_map (SheafBaseChange.Construction.Schemes.baseChangeFppfAb f)
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor T) (SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f)
      (fun a => sheafDualBaseChangeIso_natural f a) e.rightAdjoint H
  change _ = kernelSubobject ((baseChangePairing f e).rightAdjoint ≫
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor T).map (baseChangeSubobject f H).arrow.op)
  rw [baseChangePairing_rightAdjoint]
  exact h

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AnnihilatorBaseChange
