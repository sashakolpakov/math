import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Flat

/-! # Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.Support

noncomputable section

/-! An open reduced support has the ambient local ring at every point.
In particular this applies to codimension-zero supports of a smooth
projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem inclusion_isOpenImmersion {X : Scheme} [IsReduced X]
    (W : IrreducibleCloseds X) (hW : IsOpen (W : Set X)) :
    IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
  let U : X.Opens := ⟨W, hW⟩
  have hr : Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) ⊆ Set.range U.ι := by
    rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι, Scheme.Opens.range_ι]
    exact fun _ h => h
  let j := IsOpenImmersion.lift U.ι (CycleClass.Geometric.GenericPoint.reducedSupportι W) hr
  have hj : j ≫ U.ι = CycleClass.Geometric.GenericPoint.reducedSupportι W := IsOpenImmersion.lift_fac _ _ hr
  let : IsClosedImmersion (j ≫ U.ι) := hj ▸ inferInstance
  let : IsClosedImmersion j := IsClosedImmersion.of_comp j U.ι
  let : Surjective j := ⟨by
    intro x
    have hx : x.1 ∈ (W : Set X) := x.property
    obtain ⟨y, hy⟩ := (CycleClass.Geometric.GenericPoint.range_reducedSupportι W).symm ▸ hx
    refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun f : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ X => f y) hj).trans hy⟩
  let : IsIso j := isIso_of_isClosedImmersion_of_surjective j
  rw [← hj]
  infer_instance

def localModuleEquiv {X : Scheme} (W : IrreducibleCloseds X)
    [IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι W)] (x : X) (hx : x ∈ (W : Set X)) :
    CycleClass.Thom.IntersectionGeometry.localSupportModule X W x hx ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx
  let f : X.presheaf.stalk x ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y :=
    eqToHom (congrArg (fun t => X.presheaf.stalk t)
      (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm) ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap y
  let := f.hom.toAlgebra
  exact (AlgEquiv.ofBijective (Algebra.ofId (X.presheaf.stalk x)
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y))
    (ConcreteCategory.bijective_of_isIso f)).symm.toLinearEquiv

theorem localModule_length_at_generic {X : Scheme} (W : IrreducibleCloseds X)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ (W : Set X)) :
    Module.length (X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint W))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hx) = 1 := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint W
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx
  have hy : y = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) := by
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective
    exact (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).trans (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).symm
  let R := X.presheaf.stalk x
  let S := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y
  let f : R ⟶ S := eqToHom (congrArg (fun t => X.presheaf.stalk t)
    (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm) ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap y
  let := f.hom.toAlgebra
  have hlen (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (hz : z = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) :
      Module.length ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk z)
        ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk z) = 1 := by
    subst z
    exact Module.length_eq_one (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField
  have hf : Function.Surjective f :=
    ((CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap_surjective y).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg
        (fun t => X.presheaf.stalk t) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm))).surjective
  change Module.length R S = 1
  rw [Module.length_eq_of_surjective (M := S) hf]
  exact hlen y hy

theorem codimension_zero_isOpen (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 0) :
    IsOpen (A.val : Set X.carrier) := by
  let C := X.supportComponent A.val
  let D : IrreducibleCloseds X.carrier :=
    ⟨C.val, C.property.1, isClosed_of_mem_irreducibleComponents _ C.property⟩
  have hAD : A.val ≤ D := X.support_subset_component A.val
  have he : A.val = D := by
    by_contra hne
    have h := Supports.codimension_strictAnti X m (lt_of_le_of_ne hAD hne)
    rw [A.property] at h
    omega
  rw [he]
  exact Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains X.stalk_isDomain
    (NoetherianSpace.finite_irreducibleComponents (α := X.carrier)) C.property

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.Support
