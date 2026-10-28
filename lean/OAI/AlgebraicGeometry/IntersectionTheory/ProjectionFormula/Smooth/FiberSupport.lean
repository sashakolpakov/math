import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

/-! # Fiber Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.FiberSupport

noncomputable section

/-! At a smooth morphism, an irreducible support containing the whole
fiber and mapping generically to its base point has the exact closed-fiber
ideal in the ambient stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

variable {X Y : Scheme} (f : X ⟶ Y) [Smooth f] (x : X)

def prime : Spec (X.presheaf.stalk x) :=
  ⟨(IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom, by
    let := StalkFiber.quotient_domain f x
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance⟩

theorem comap_prime : (Spec.map (f.stalkMap x)) (prime f x) =
    IsLocalRing.closedPoint (Y.presheaf.stalk (f x)) := by
  apply PrimeSpectrum.ext
  apply Eq.symm
  apply (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    ((prime f x).isPrime.comap (f.stalkMap x).hom).ne_top
  exact Ideal.le_comap_map

theorem image_prime : f (X.fromSpecStalk x (prime f x)) = f x := by
  have he := congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ Y => g (prime f x))
    (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x))
  change Y.fromSpecStalk (f x) ((Spec.map (f.stalkMap x)) (prime f x)) =
    f (X.fromSpecStalk x (prime f x)) at he
  rw [comap_prime, Scheme.fromSpecStalk_closedPoint] at he
  exact he.symm

theorem kernel_eq (W : IrreducibleCloseds X) (hx : x ∈ (W : Set X))
    (hgeneric : f (CycleClass.Thom.IntersectionGeometry.supportPoint W) = f x)
    (hfiber : ∀ z : X, f z = f x → z ∈ (W : Set X)) :
    RingHom.ker (Local.Principal.supportStalkMap X W x hx).hom =
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom := by
  let q := Stalk.PrimeQuotient.kernelPrime X W x hx
  have hq : (Spec.map (f.stalkMap x)) q =
      IsLocalRing.closedPoint (Y.presheaf.stalk (f x)) := by
    apply (Y.fromSpecStalk (f x)).isEmbedding.injective
    have he := congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ Y => g q)
      (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x))
    change Y.fromSpecStalk (f x) ((Spec.map (f.stalkMap x)) q) =
      f (X.fromSpecStalk x q) at he
    rw [Stalk.PrimeQuotient.kernelPrime_image, hgeneric] at he
    exact he.trans Scheme.fromSpecStalk_closedPoint.symm
  have hpq : (prime f x).asIdeal ≤ q.asIdeal := by
    change (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom ≤ q.asIdeal
    apply Ideal.map_le_iff_le_comap.mpr
    exact (congrArg PrimeSpectrum.asIdeal hq).symm.le
  have hqp : q.asIdeal ≤ (prime f x).asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes q (prime f x)).mpr
    apply (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.mp
    change X.fromSpecStalk x (Stalk.PrimeQuotient.kernelPrime X W x hx) ⤳ X.fromSpecStalk x (prime f x)
    rw [Stalk.PrimeQuotient.kernelPrime_image]
    exact (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).specializes
      (hfiber _ (image_prime f x))
  exact le_antisymm hqp hpq

def moduleEquiv (W : IrreducibleCloseds X) (hx : x ∈ (W : Set X))
    (hgeneric : f (CycleClass.Thom.IntersectionGeometry.supportPoint W) = f x)
    (hfiber : ∀ z : X, f z = f x → z ∈ (W : Set X)) :
    CycleClass.Thom.IntersectionGeometry.localSupportModule X W x hx ≃ₗ[X.presheaf.stalk x]
      ((X.presheaf.stalk x) ⧸
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom) := by
  let q := Stalk.PrimeQuotient.kernelPrime X W x hx
  exact (Stalk.PrimeQuotient.moduleEquiv X W x hx q (Stalk.PrimeQuotient.kernelPrime_image X W x hx)).trans
    (Submodule.quotEquivOfEq _ _ (kernel_eq f x W hx hgeneric hfiber))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.FiberSupport
