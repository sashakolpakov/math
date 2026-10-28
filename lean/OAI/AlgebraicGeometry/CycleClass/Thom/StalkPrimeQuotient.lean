import OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule

/-! # Stalk Prime Quotient -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient

/-! A prime of an ambient stalk is the exact kernel of the local module
of the closure of its image. Thus its quotient is the native ThomClass support module. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions

def kernelPrime (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X)) :
    Spec (X.presheaf.stalk x) :=
  ⟨RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X W x hx).hom,
    Ideal.isPrime_bot.comap (SupportStalkModule.Constructions.supportStalkMap X W x hx).hom⟩

theorem kernelPrime_image (X : Scheme) (W : IrreducibleCloseds X) (x : X)
    (hx : x ∈ (W : Set X)) :
    X.fromSpecStalk x (kernelPrime X W x hx) = IntersectionGeometry.supportPoint W := by
  let Y := Geometric.GenericPoint.reducedSupportScheme W
  let y := IntersectionGeometry.supportPreimage W x hx
  let T := Y.presheaf.stalk y
  let σ := SupportStalkModule.Constructions.supportStalkMap X W x hx
  have hs := TorAlgebra.LocalSupportSpectrum.stalkMap_square (Geometric.GenericPoint.reducedSupportι W) y x
    (IntersectionGeometry.supportPreimage_spec W x hx)
  have he := congrArg (fun f : Spec T ⟶ X => f (genericPoint (Spec T))) hs
  change X.fromSpecStalk x ((Spec.map σ) (genericPoint (Spec T))) =
    Geometric.GenericPoint.reducedSupportι W (Y.fromSpecStalk y (genericPoint (Spec T))) at he
  rw [SupportStalkModule.Constructions.genericPoint_image, Geometric.GenericPoint.reducedSupport_genericPoint_eq] at he
  rw [genericPoint_eq_bot_of_affine] at he
  exact he

theorem kernel_eq (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X))
    (p : Spec (X.presheaf.stalk x)) (hp : X.fromSpecStalk x p = IntersectionGeometry.supportPoint W) :
    RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X W x hx).hom = p.asIdeal := by
  have hprime : kernelPrime X W x hx = p :=
    (X.fromSpecStalk x).isEmbedding.injective ((kernelPrime_image X W x hx).trans hp.symm)
  exact congrArg PrimeSpectrum.asIdeal hprime

def moduleEquiv (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X))
    (p : Spec (X.presheaf.stalk x)) (hp : X.fromSpecStalk x p = IntersectionGeometry.supportPoint W) :
    IntersectionGeometry.localSupportModule X W x hx ≃ₗ[X.presheaf.stalk x] (X.presheaf.stalk x ⧸ p.asIdeal) := by
  let R := X.presheaf.stalk x
  let T := (Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (IntersectionGeometry.supportPreimage W x hx)
  let σ := SupportStalkModule.Constructions.supportStalkMap X W x hx
  let : Algebra R T := σ.hom.toAlgebra
  have hσ : Function.Surjective (Algebra.ofId R T) := SupportStalkModule.Constructions.supportStalkMap_surjective X W x hx
  exact (Ideal.quotientKerAlgEquivOfSurjective hσ).symm.toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ (kernel_eq X W x hx p hp))

end Constructions

end AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient

namespace AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme

/-! The prime quotient of the actual ambient stalk maps canonically
into its original reduced support. Its spectrum points give the actual
global irreducible supports used in the principal cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme) (D : IrreducibleCloseds X) (x : X) (hxD : x ∈ (D : Set X))

abbrev quotientRing := X.presheaf.stalk x ⧸ (kernelPrime X D x hxD).asIdeal

instance quotientRing_isDomain : IsDomain (quotientRing X D x hxD) := by
  let : (kernelPrime X D x hxD).asIdeal.IsPrime := (kernelPrime X D x hxD).isPrime
  infer_instance

def quotientStalkEquiv : quotientRing X D x hxD ≃+*
    (Geometric.GenericPoint.reducedSupportScheme D).presheaf.stalk (IntersectionGeometry.supportPreimage D x hxD) :=
  (SupportStalkModule.Constructions.supportStalkMap X D x hxD).hom.quotientKerEquivOfSurjective (SupportStalkModule.Constructions.supportStalkMap_surjective X D x hxD)

theorem quotientStalkEquiv_symm_apply (r : X.presheaf.stalk x) :
    (quotientStalkEquiv X D x hxD).symm (SupportStalkModule.Constructions.supportStalkMap X D x hxD r) =
      algebraMap (X.presheaf.stalk x) (quotientRing X D x hxD) r :=
  RingHom.quotientKerEquivOfSurjective_symm_apply (SupportStalkModule.Constructions.supportStalkMap_surjective X D x hxD) r

def quotientSupportMap : Spec (.of (quotientRing X D x hxD)) ⟶ Geometric.GenericPoint.reducedSupportScheme D :=
  Spec.map (quotientStalkEquiv X D x hxD).symm.toCommRingCatIso.hom ≫
    (Geometric.GenericPoint.reducedSupportScheme D).fromSpecStalk (IntersectionGeometry.supportPreimage D x hxD)

theorem quotientSupportMap_ambient : quotientSupportMap X D x hxD ≫ Geometric.GenericPoint.reducedSupportι D =
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (quotientRing X D x hxD))) ≫ X.fromSpecStalk x := by
  have hσ : SupportStalkModule.Constructions.supportStalkMap X D x hxD ≫ (quotientStalkEquiv X D x hxD).symm.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (quotientRing X D x hxD)) := by
    ext r
    exact quotientStalkEquiv_symm_apply X D x hxD r
  have hs := TorAlgebra.LocalSupportSpectrum.stalkMap_square (Geometric.GenericPoint.reducedSupportι D) (IntersectionGeometry.supportPreimage D x hxD) x
    (IntersectionGeometry.supportPreimage_spec D x hxD)
  change Spec.map (SupportStalkModule.Constructions.supportStalkMap X D x hxD) ≫ X.fromSpecStalk x =
    (Geometric.GenericPoint.reducedSupportScheme D).fromSpecStalk (IntersectionGeometry.supportPreimage D x hxD) ≫ Geometric.GenericPoint.reducedSupportι D at hs
  rw [quotientSupportMap, Category.assoc, ← hs, ← Category.assoc, ← Spec.map_comp, hσ]

def quotientSupport (q : Spec (.of (quotientRing X D x hxD))) : IrreducibleCloseds X :=
  irreducibleSetEquivPoints.symm (Geometric.GenericPoint.reducedSupportι D (quotientSupportMap X D x hxD q))

theorem supportPoint_quotientSupport (q : Spec (.of (quotientRing X D x hxD))) :
    IntersectionGeometry.supportPoint (quotientSupport X D x hxD q) = Geometric.GenericPoint.reducedSupportι D (quotientSupportMap X D x hxD q) :=
  irreducibleSetEquivPoints.apply_symm_apply _

theorem quotientSupport_mem_parent (q : Spec (.of (quotientRing X D x hxD))) :
    IntersectionGeometry.supportPoint (quotientSupport X D x hxD q) ∈ (D : Set X) := by
  rw [supportPoint_quotientSupport, ← Geometric.GenericPoint.range_reducedSupportι]
  exact ⟨_, rfl⟩

theorem quotientSupport_preimage (q : Spec (.of (quotientRing X D x hxD))) :
    quotientSupportMap X D x hxD q = IntersectionGeometry.supportPreimage D (IntersectionGeometry.supportPoint (quotientSupport X D x hxD q))
      (quotientSupport_mem_parent X D x hxD q) := by
  apply (Geometric.GenericPoint.reducedSupportι D).isClosedEmbedding.injective
  exact (supportPoint_quotientSupport X D x hxD q).symm.trans (IntersectionGeometry.supportPreimage_spec D _ _).symm

end AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme

end

end OAI
