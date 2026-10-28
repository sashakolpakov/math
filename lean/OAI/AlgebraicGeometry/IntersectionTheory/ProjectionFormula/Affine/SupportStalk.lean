import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
import Mathlib.RingTheory.Localization.Ideal

/-! # Support Stalk -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

noncomputable section

/-! The native reduced support of an affine prime has, at every
specialization, the quotient of the ambient stalk by the extended
prime ideal. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable (R : Type) [CommRing R]

def support (q : PrimeSpectrum R) : IrreducibleCloseds (Spec (.of R)) :=
  irreducibleSetEquivPoints.symm q

theorem point (q : PrimeSpectrum R) : CycleClass.Thom.IntersectionGeometry.supportPoint (support R q) = q :=
  (irreducibleSetEquivPoints (α := (Spec (.of R)))).apply_symm_apply q

theorem mem (q p : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) : p ∈ (support R q : Set (Spec (.of R))) := by
  change p ∈ closure ({q} : Set (Spec (.of R)))
  exact specializes_iff_mem_closure.mp ((PrimeSpectrum.le_iff_specializes q p).mp hqp)

theorem kernel_comap (q p : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    (Stalk.PrimeQuotient.kernelPrime (Spec (.of R)) (support R q) p (mem R q p hqp)).asIdeal.comap
      (StructureSheaf.toStalk R p).hom = q.asIdeal := by
  have h := Stalk.PrimeQuotient.kernelPrime_image (Spec (.of R)) (support R q) p (mem R q p hqp)
  rw [point, Spec.fromSpecStalk_eq'] at h
  exact congrArg PrimeSpectrum.asIdeal h

theorem kernel_map (q p : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    q.asIdeal.map (StructureSheaf.toStalk R p).hom =
      (Stalk.PrimeQuotient.kernelPrime (Spec (.of R)) (support R q) p (mem R q p hqp)).asIdeal := by
  let : Algebra R ((Spec (.of R)).presheaf.stalk p) := (StructureSheaf.toStalk R p).hom.toAlgebra
  let : IsLocalization p.asIdeal.primeCompl ((Spec (.of R)).presheaf.stalk p) := by
    change IsLocalization p.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk p)
    infer_instance
  have h := IsLocalization.map_under p.asIdeal.primeCompl
    ((Spec (.of R)).presheaf.stalk p)
    (Stalk.PrimeQuotient.kernelPrime (Spec (.of R)) (support R q) p (mem R q p hqp)).asIdeal
  change ((Stalk.PrimeQuotient.kernelPrime (Spec (.of R)) (support R q) p (mem R q p hqp)).asIdeal.comap
    (StructureSheaf.toStalk R p).hom).map (StructureSheaf.toStalk R p).hom = _ at h
  rwa [kernel_comap R q p hqp] at h

def moduleEquiv (q p : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (support R q) p (mem R q p hqp) ≃ₗ[
      (Spec (.of R)).presheaf.stalk p]
    ((Spec (.of R)).presheaf.stalk p ⧸ q.asIdeal.map (StructureSheaf.toStalk R p).hom) :=
  (Stalk.PrimeQuotient.moduleEquiv (Spec (.of R)) (support R q) p (mem R q p hqp)
    (Stalk.PrimeQuotient.kernelPrime (Spec (.of R)) (support R q) p (mem R q p hqp))
    (Stalk.PrimeQuotient.kernelPrime_image (Spec (.of R)) (support R q) p (mem R q p hqp))).trans
      (Submodule.quotEquivOfEq _ _ (kernel_map R q p hqp).symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk
