import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportKernel

/-! # Spec Support Kernel -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SpecSupportKernel.Constructions

noncomputable section

/-! For every irreducible closed support of an affine spectrum, its
native reduced-support stalk kernel is the localization of the actual
generic-point prime ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImageStalkKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportKernel.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : CommRingCat) (P : PrimeSpectrum R)

local instance : P.asIdeal.IsPrime := P.isPrime

def primeSupport : IrreducibleCloseds (Spec R) :=
  Geometric.StratumClosure.integralImageClosure (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P.asIdeal)))

theorem primeSupport_genericPoint : IntersectionGeometry.supportPoint (primeSupport R P) = P := by
  unfold primeSupport
  rw [Closed.ImageStalkKernel.Constructions.imageClosure_genericPoint, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact Ideal.mk_ker

theorem primeSupport_eq (A : IrreducibleCloseds (Spec R)) : primeSupport R (IntersectionGeometry.supportPoint A) = A :=
  irreducibleSetEquivPoints.injective (primeSupport_genericPoint R (IntersectionGeometry.supportPoint A))

theorem support_coe (A : IrreducibleCloseds (Spec R)) :
    (A : Set (Spec R)) = PrimeSpectrum.zeroLocus ((IntersectionGeometry.supportPoint A).asIdeal : Set R) :=
  (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).symm.trans
    (PrimeSpectrum.closure_singleton (IntersectionGeometry.supportPoint A))

theorem support_kernel (A : IrreducibleCloseds (Spec R)) (q : PrimeSpectrum R) (hq : q ∈ (A : Set (Spec R))) :
    (StalkPrimeQuotient.Constructions.kernelPrime (Spec R) A q hq).asIdeal.map (Spec.stalkIso R q).hom.hom =
      (IntersectionGeometry.supportPoint A).asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  let P := IntersectionGeometry.supportPoint A
  let : P.asIdeal.IsPrime := P.isPrime
  let f : R ⟶ CommRingCat.of (R ⧸ P.asIdeal) := CommRingCat.ofHom (Ideal.Quotient.mk P.asIdeal)
  let : IsClosedImmersion (Spec.map f) := IsClosedImmersion.spec_of_surjective f Ideal.Quotient.mk_surjective
  have hA : Geometric.StratumClosure.integralImageClosure (Spec.map f) = A := primeSupport_eq R A
  have hr : Set.range (Spec.map f) = (A : Set (Spec R)) := by
    exact (Spec.map f).isClosedEmbedding.isClosed_range.closure_eq.symm.trans
      (congrArg (fun B : IrreducibleCloseds (Spec R) => (B : Set (Spec R))) hA)
  obtain ⟨y, hy⟩ := hr.symm ▸ hq
  subst q
  have h := Affine.SupportKernel.Constructions.support_kernel_localization R (CommRingCat.of (R ⧸ P.asIdeal)) f Ideal.Quotient.mk_surjective y
  have hk : RingHom.ker f.hom = P.asIdeal := Ideal.mk_ker
  change (StalkPrimeQuotient.Constructions.kernelPrime (Spec R) A ((Spec.map f) y) hq).asIdeal.map
    (Spec.stalkIso R (y.comap f.hom)).hom.hom = P.asIdeal.map
      (algebraMap R (Localization.AtPrime (y.comap f.hom).asIdeal))
  simpa only [hA, hk] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SpecSupportKernel.Constructions
