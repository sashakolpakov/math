import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.TorFinite
import Mathlib.RingTheory.Support

/-! # Support Spectrum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportSpectrum

noncomputable section

/-! The algebraic support of a reduced-support stalk maps into its
geometric closed support under the ambient stalk's canonical spectrum map. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem stalkMap_square {Y X : Scheme} (i : Y ⟶ X) (y : Y) (x : X) (h : i y = x) :
    Spec.map (eqToHom (congrArg (fun t => X.presheaf.stalk t) h.symm) ≫ i.stalkMap y) ≫
      X.fromSpecStalk x = Y.fromSpecStalk y ≫ i := by
  subst x
  simp

theorem image_mem_support (X : Scheme) (W : IrreducibleCloseds X)
    (x : X) (hx : x ∈ (W : Set X)) (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : p ∈ Module.support (X.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule X W x hx)) :
    X.fromSpecStalk x p ∈ (W : Set X) := by
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx
  let f : X.presheaf.stalk x ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y :=
    eqToHom (congrArg (fun t => X.presheaf.stalk t)
      (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm) ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap y
  let := f.hom.toAlgebra
  have hf : Function.Surjective f :=
    ((CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap_surjective y).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg
        (fun t => X.presheaf.stalk t) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm))).surjective
  change p ∈ Module.support (X.presheaf.stalk x)
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y) at hp
  rw [Module.support_of_algebra] at hp
  have hr : p ∈ Set.range (PrimeSpectrum.comap f.hom) := by
    rw [range_comap_of_surjective _ _ hf]
    exact hp
  obtain ⟨q, hq⟩ := hr
  have hs := stalkMap_square (CycleClass.Geometric.GenericPoint.reducedSupportι W) y x (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx)
  have he := congrArg (fun j : Spec ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y) ⟶ X => j q) hs
  change X.fromSpecStalk x (PrimeSpectrum.comap f.hom q) =
    CycleClass.Geometric.GenericPoint.reducedSupportι W ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).fromSpecStalk y q) at he
  rw [hq] at he
  rw [he, ← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact ⟨_, rfl⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportSpectrum
