import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ParameterProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Tuple Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.TupleRepresentation.Core

noncomputable section

/-! Represent finite tuples satisfying componentwise subfunctor
conditions by the explicit finite product of their representing schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {n : ℕ}

def finiteTupleSubfunctor (G : Fin n → Subfunctor F) : Subfunctor (Has.Core.tupleFunctor F n) where
  obj T := {f | ∀ i, f i ∈ (G i).obj T}
  map a _f hf i := (G i).map a (hf i)

variable (G : Fin n → Subfunctor F) (H : Fin n → Over S)
variable (e : ∀ i, yoneda.obj (H i) ≅ (G i).toFunctor)

def finiteTupleRepresentationMap : yoneda.obj (ParameterProducts.Core.finiteParameterProduct n H) ⟶
    (finiteTupleSubfunctor G).toFunctor where
  app T := ↾fun f => ⟨fun i => ((e i).hom.app T (f ≫ ParameterProducts.Core.finiteParameterProjection H i)).val,
    fun i => ((e i).hom.app T (f ≫ ParameterProducts.Core.finiteParameterProjection H i)).property⟩
  naturality T U a := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    funext i
    have h := congrArg Subtype.val
      (ConcreteCategory.congr_hom ((e i).hom.naturality a)
        (show T.unop ⟶ H i from f ≫ ParameterProducts.Core.finiteParameterProjection H i))
    change ((e i).hom.app U (a.unop ≫ (f ≫ ParameterProducts.Core.finiteParameterProjection H i))).val =
      F.map a ((e i).hom.app T (f ≫ ParameterProducts.Core.finiteParameterProjection H i)).val at h
    change ((e i).hom.app U ((a.unop ≫ f) ≫ ParameterProducts.Core.finiteParameterProjection H i)).val =
      F.map a ((e i).hom.app T (f ≫ ParameterProducts.Core.finiteParameterProjection H i)).val
    exact (congrArg (fun k => ((e i).hom.app U k).val)
      (Category.assoc a.unop f (ParameterProducts.Core.finiteParameterProjection H i))).trans h

instance finiteTupleRepresentationMap_isIso : IsIso (finiteTupleRepresentationMap G H e) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro T
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro f g h
    apply ParameterProducts.Core.finiteParameter_hom_ext H
    intro i
    apply (CategoryTheory.mono_iff_injective ((e i).hom.app T)).mp inferInstance
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val h) i
  · intro z
    let f : ∀ i, T.unop ⟶ H i := fun i => (e i).inv.app T ⟨z.val i, z.property i⟩
    refine ⟨ParameterProducts.Core.finiteParameterLift H f, Subtype.ext ?_⟩
    funext i
    change ((e i).hom.app T (ParameterProducts.Core.finiteParameterLift H f ≫ ParameterProducts.Core.finiteParameterProjection H i)).val = z.val i
    rw [ParameterProducts.Core.finiteParameterLift_projection]
    exact congrArg Subtype.val (((e i).app T).inv_hom_id_apply ⟨z.val i, z.property i⟩)

def finiteTupleRepresentation : yoneda.obj (ParameterProducts.Core.finiteParameterProduct n H) ≅
    (finiteTupleSubfunctor G).toFunctor := asIso (finiteTupleRepresentationMap G H e)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.TupleRepresentation.Core
