import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Stalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.KernelSquare
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkProperties

/-! # Module Square -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.ModuleSquare

noncomputable section

section

/-! Local support modules transport through an actual isomorphism
of reduced supports over an ambient morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

variable {X Y : Scheme} (f : X ⟶ Y) (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
  (g : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme B)
  (h : CycleClass.Geometric.GenericPoint.reducedSupportι A ≫ f = g ≫ CycleClass.Geometric.GenericPoint.reducedSupportι B)
  (x : X) (hxA : x ∈ (A : Set X)) (hxB : f x ∈ (B : Set Y))

include h in
theorem point : g (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) = CycleClass.Thom.IntersectionGeometry.supportPreimage B (f x) hxB := by
  apply (CycleClass.Geometric.GenericPoint.reducedSupportι B).isClosedEmbedding.injective
  exact (congrArg (fun k : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ Y => k (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA)) h).symm.trans
    ((congrArg f (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec A x hxA)).trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec B (f x) hxB).symm)

def map : (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B (f x) hxB) ⟶
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) :=
  eqToHom (congrArg (fun y => (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk y)
    (point f A B g h x hxA hxB).symm) ≫ g.stalkMap (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA)

instance [IsIso g] : IsIso (map f A B g h x hxA hxB) := by unfold map; infer_instance

theorem square : Local.Principal.supportStalkMap Y B (f x) hxB ≫ map f A B g h x hxA hxB =
    f.stalkMap x ≫ Local.Principal.supportStalkMap X A x hxA := by
  have aux (a : CycleClass.Geometric.GenericPoint.reducedSupportScheme A) (b : CycleClass.Geometric.GenericPoint.reducedSupportScheme B) (z : X)
      (ha : CycleClass.Geometric.GenericPoint.reducedSupportι A a = z) (hb : g a = b) (hc : CycleClass.Geometric.GenericPoint.reducedSupportι B b = f z) :
      (eqToHom (congrArg (fun y => Y.presheaf.stalk y) hc.symm) ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι B).stalkMap b) ≫
        (eqToHom (congrArg (fun y => (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk y) hb.symm) ≫ g.stalkMap a) =
      f.stalkMap z ≫ (eqToHom (congrArg (fun z => X.presheaf.stalk z) ha.symm) ≫
        (CycleClass.Geometric.GenericPoint.reducedSupportι A).stalkMap a) := by
    subst z
    subst b
    simpa only [eqToHom_refl, Category.id_comp, Stalk.KernelSquare.map] using
      Stalk.KernelSquare.square f (CycleClass.Geometric.GenericPoint.reducedSupportι B) g (CycleClass.Geometric.GenericPoint.reducedSupportι A) h a
  exact aux (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) (CycleClass.Thom.IntersectionGeometry.supportPreimage B (f x) hxB) x
    (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec A x hxA) (point f A B g h x hxA hxB) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec B (f x) hxB)

def equiv [IsIso g] :
    CycleClass.Thom.IntersectionGeometry.localSupportModule Y B (f x) hxB ≃ₗ[Y.presheaf.stalk (f x)]
      (ModuleCat.restrictScalars (f.stalkMap x).hom).obj (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hxA) := by
  let e := (asIso (map f A B g h x hxA hxB)).commRingCatIsoToRingEquiv
  exact
    { e.toAddEquiv with
      map_smul' := by
        intro r t
        change e (Local.Principal.supportStalkMap Y B (f x) hxB r *
          (show (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B (f x) hxB) from t)) =
          Local.Principal.supportStalkMap X A x hxA (f.stalkMap x r) * e t
        rw [map_mul]
        congr 1
        exact congrArg (fun k : Y.presheaf.stalk (f x) ⟶
          (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) => k r)
          (square f A B g h x hxA hxB) }

end

/-! The actual local ring map in a commuting support square
inherits the etale properties of an open support neighborhood. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Stalk

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.ModuleSquare

variable {X Y : Scheme} (f : X ⟶ Y) (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
  (g : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme B)
  (h : CycleClass.Geometric.GenericPoint.reducedSupportι A ≫ f = g ≫ CycleClass.Geometric.GenericPoint.reducedSupportι B)
  (x : X) (hxA : x ∈ (A : Set X)) (hxB : f x ∈ (B : Set Y))

theorem localHom : IsLocalHom (map f A B g h x hxA hxB).hom := by
  let a := CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA
  let e := eqToHom (congrArg (fun y => (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk y)
    (point f A B g h x hxA hxB).symm)
  let : IsLocalHom e.hom := IsLocalHom.of_surjective _ (ConcreteCategory.bijective_of_isIso e).surjective
  let : IsLocalHom (g.stalkMap a).hom := g.toLRSHom.prop a
  change IsLocalHom ((g.stalkMap a).hom.comp e.hom)
  infer_instance

theorem properties (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).Opens) [Etale (U.ι ≫ g)]
    (hxU : CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA ∈ U) :
    (map f A B g h x hxA hxB).hom.Flat ∧ (map f A B g h x hxA hxB).hom.FormallyUnramified ∧
      (map f A B g h x hxA hxB).hom.EssFiniteType := by
  have H := ProjectionFormula.Etale.StalkProperties.of_open g U (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) hxU
  unfold map
  exact ⟨(RingHom.Flat.respectsIso.cancel_left_isIso _ _).mpr H.1,
    (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso _ _).mpr H.2.1,
    (RingHom.EssFiniteType.respectsIso.cancel_left_isIso _ _).mpr H.2.2⟩

end Stalk

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.ModuleSquare
