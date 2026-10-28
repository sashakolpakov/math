import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Tor
import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry

/-! # Tor Finite -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.TorFinite

noncomputable section

/-! Finiteness of the actual local support modules and of ThomClass's
categorical local Tor modules over a locally Noetherian ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem localSupportModule_finite (X : Scheme) (W : IrreducibleCloseds X)
    (x : X) (hx : x ∈ (W : Set X)) :
    Module.Finite (X.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule X W x hx) := by
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx
  let f : X.presheaf.stalk x ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y :=
    eqToHom (congrArg (fun t => X.presheaf.stalk t)
      (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm) ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap y
  let := f.hom.toAlgebra
  have hf : Function.Surjective f :=
    ((CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap_surjective y).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg
        (fun t => X.presheaf.stalk t) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm))).surjective
  exact Module.Finite.of_surjective (Algebra.ofId (X.presheaf.stalk x)
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y)).toLinearMap hf

theorem localTor_finite (X : Scheme) [IsLocallyNoetherian X]
    (A B : IrreducibleCloseds X) (x : X) (hxA : x ∈ (A : Set X))
    (hxB : x ∈ (B : Set X)) (n : ℕ) :
    Module.Finite (X.presheaf.stalk x)
      (((Tor (ModuleCat (X.presheaf.stalk x)) n).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hxA)).obj (CycleClass.Thom.IntersectionGeometry.localSupportModule X B x hxB)) := by
  let := localSupportModule_finite X A x hxA
  let := localSupportModule_finite X B x hxB
  exact ProjectionFormula.Finite.Tor.finite _ _ _ n

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.TorFinite
