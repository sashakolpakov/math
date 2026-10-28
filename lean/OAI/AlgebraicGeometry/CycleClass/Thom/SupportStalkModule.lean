import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalSupportSpectrum

/-! # Support Stalk Module -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions

noncomputable section

/-! The actual reduced-support stalk map and its generic point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
universe u

def supportStalkMap (X : Scheme) (W : IrreducibleCloseds X) (x : X)
    (hx : x ∈ (W : Set X)) :
    X.presheaf.stalk x ⟶ (Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (IntersectionGeometry.supportPreimage W x hx) :=
  eqToHom (congrArg (fun t => X.presheaf.stalk t) (IntersectionGeometry.supportPreimage_spec W x hx).symm) ≫
    (Geometric.GenericPoint.reducedSupportι W).stalkMap (IntersectionGeometry.supportPreimage W x hx)

theorem supportStalkMap_surjective (X : Scheme) (W : IrreducibleCloseds X) (x : X)
    (hx : x ∈ (W : Set X)) : Function.Surjective (supportStalkMap X W x hx) :=
  ((Geometric.GenericPoint.reducedSupportι W).stalkMap_surjective _).comp
    (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg
      (fun t => X.presheaf.stalk t) (IntersectionGeometry.supportPreimage_spec W x hx).symm))).surjective

theorem genericPoint_image (X : Scheme.{u}) [IsIntegral X] (x : X) :
    X.fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x))) = genericPoint X := by
  have hmem : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  obtain ⟨p, hp⟩ := hmem
  apply Inseparable.eq
  apply Specializes.antisymm
  · rw [← hp]
    exact ((genericPoint_spec (Spec (X.presheaf.stalk x))).specializes trivial).map
      (X.fromSpecStalk x).continuous
  · exact (genericPoint_spec X).specializes trivial

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions
