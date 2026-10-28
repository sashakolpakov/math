import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.FiberSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Stalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.TransverseEuler

/-! # Fiber Multiplicity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.FiberMultiplicity

noncomputable section

/-! Native local intersection coefficient one for a smooth fiber
support against a support whose projection is etale at the intersection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

variable {X Y : Scheme} (f : X ⟶ Y) [Smooth f]
  (A B : IrreducibleCloseds X) (x : X)
  (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X))

theorem euler_one (hgeneric : f (CycleClass.Thom.IntersectionGeometry.supportPoint A) = f x)
    (hfiber : ∀ z : X, f z = f x → z ∈ (A : Set X))
    (hB : (Support.Stalk.Projection.map f B x hxB).hom.Flat ∧
      (Support.Stalk.Projection.map f B x hxB).hom.FormallyUnramified ∧
      (Support.Stalk.Projection.map f B x hxB).hom.EssFiniteType) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * (CycleClass.Thom.IntersectionGeometry.localTorLength X A B x hxA hxB i).toNat) = 1 := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B x hxB)
  let σ := Local.Principal.supportStalkMap X B x hxB
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let : Algebra S T := σ.hom.toAlgebra
  let : Algebra R T := (Support.Stalk.Projection.map f B x hxB).hom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Flat R S := Flat.stalkMap f x
  let : Module.Flat R T := hB.1
  let : Algebra.FormallyUnramified R T := hB.2.1
  let : Algebra.EssFiniteType R T := hB.2.2
  have hσ : Function.Surjective (algebraMap S T) := Local.Principal.supportStalkMap_surjective X B x hxB
  let : IsLocalHom (f.stalkMap x).hom := f.toLRSHom.prop x
  let : IsLocalHom σ.hom := IsLocalHom.of_surjective _ hσ
  let : IsLocalHom (algebraMap R T) := by
    change IsLocalHom (σ.hom.comp (f.stalkMap x).hom)
    infer_instance
  let e := FiberSupport.moduleEquiv f x A hxA hgeneric hfiber
  have he (i : ℕ) := Open.SupportTor.length_iso S e.toModuleIso
    (Iso.refl (CycleClass.Thom.IntersectionGeometry.localSupportModule X B x hxB)) i
  change (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
    (Module.length S (((Tor (ModuleCat S) i).obj (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hxA)).obj
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X B x hxB))).toNat) = 1
  simp_rw [he]
  exact ProjectionFormula.Flat.TransverseEuler.euler_one_of_unramified R S T hσ d

theorem euler_one_of_etale_open (hgeneric : f (CycleClass.Thom.IntersectionGeometry.supportPoint A) = f x)
    (hfiber : ∀ z : X, f z = f x → z ∈ (A : Set X))
    (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).Opens) [Etale (U.ι ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ f))]
    (hu : CycleClass.Thom.IntersectionGeometry.supportPreimage B x hxB ∈ U) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * (CycleClass.Thom.IntersectionGeometry.localTorLength X A B x hxA hxB i).toNat) = 1 :=
  euler_one f A B x hxA hxB hgeneric hfiber (Support.Stalk.Projection.of_etale_open f B x hxB U hu) d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.FiberMultiplicity
