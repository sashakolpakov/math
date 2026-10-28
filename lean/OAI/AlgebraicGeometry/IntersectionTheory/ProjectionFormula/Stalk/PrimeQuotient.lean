import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.Localization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportSpectrum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

/-! # Prime Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

noncomputable section

/-! A prime of an ambient stalk is the exact kernel of the local module
of the closure of its image. Thus its quotient is the native ThomClass support module. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

def kernelPrime (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X)) :
    Spec (X.presheaf.stalk x) :=
  ⟨RingHom.ker (Local.Principal.supportStalkMap X W x hx).hom,
    Ideal.isPrime_bot.comap (Local.Principal.supportStalkMap X W x hx).hom⟩

theorem kernelPrime_image (X : Scheme) (W : IrreducibleCloseds X) (x : X)
    (hx : x ∈ (W : Set X)) :
    X.fromSpecStalk x (kernelPrime X W x hx) = CycleClass.Thom.IntersectionGeometry.supportPoint W := by
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx
  let T := Y.presheaf.stalk y
  let σ := Local.Principal.supportStalkMap X W x hx
  have hs := Local.SupportSpectrum.stalkMap_square (CycleClass.Geometric.GenericPoint.reducedSupportι W) y x
    (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx)
  have he := congrArg (fun f : Spec T ⟶ X => f (genericPoint (Spec T))) hs
  change X.fromSpecStalk x ((Spec.map σ) (genericPoint (Spec T))) =
    CycleClass.Geometric.GenericPoint.reducedSupportι W (Y.fromSpecStalk y (genericPoint (Spec T))) at he
  rw [Localization.genericPoint_image, CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq] at he
  rw [genericPoint_eq_bot_of_affine] at he
  exact he

theorem kernel_eq (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X))
    (p : Spec (X.presheaf.stalk x)) (hp : X.fromSpecStalk x p = CycleClass.Thom.IntersectionGeometry.supportPoint W) :
    RingHom.ker (Local.Principal.supportStalkMap X W x hx).hom = p.asIdeal := by
  have hprime : kernelPrime X W x hx = p :=
    (X.fromSpecStalk x).isEmbedding.injective ((kernelPrime_image X W x hx).trans hp.symm)
  exact congrArg PrimeSpectrum.asIdeal hprime

def moduleEquiv (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X))
    (p : Spec (X.presheaf.stalk x)) (hp : X.fromSpecStalk x p = CycleClass.Thom.IntersectionGeometry.supportPoint W) :
    CycleClass.Thom.IntersectionGeometry.localSupportModule X W x hx ≃ₗ[X.presheaf.stalk x] (X.presheaf.stalk x ⧸ p.asIdeal) := by
  let R := X.presheaf.stalk x
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx)
  let σ := Local.Principal.supportStalkMap X W x hx
  let : Algebra R T := σ.hom.toAlgebra
  have hσ : Function.Surjective (Algebra.ofId R T) := Local.Principal.supportStalkMap_surjective X W x hx
  exact (Ideal.quotientKerAlgEquivOfSurjective hσ).symm.toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ (kernel_eq X W x hx p hp))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
