import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Cycle Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CycleSpecialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: specialization of finite affine cycles

An integral cycle in Spec R is indexed by a prime ideal P. Deform R/P
along the image of I, take the effective divisor of t, and push the
resulting cone cycle along the actual closed immersion into C_I(Spec R).
Extending this construction linearly gives specialization on finite
rational cycles. Compatibility with rational equivalence and dimension
gradings is not assumed here.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem deformationSpecialMap_surjective (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : Function.Surjective f) (hJ : I.map f = J) (hIJ : I ≤ J.comap f) :
    Function.Surjective (Deformation.Maps.BundleCycles.deformationSpecialMap I J f hIJ) :=
  Ideal.quotientMap_surjective (Deformation.ClosedSupport.BundleCycles.deformationMap_surjective I J f hf hJ hIJ)

/-- The induced map on cone rings is surjective for a closed base immersion. -/
theorem normalConeMap_surjective (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : Function.Surjective f) (hJ : I.map f = J) (hIJ : I ≤ J.comap f) :
    Function.Surjective (Deformation.Maps.BundleCycles.normalConeMap I J f hIJ) := by
  intro y
  obtain ⟨x, hx⟩ := deformationSpecialMap_surjective I J f hf hJ hIJ
    (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J y)
  refine ⟨(SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm x, (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J).injective ?_⟩
  exact (Deformation.Maps.BundleCycles.normalConeSpecialFiberEquiv_natural I J f hIJ _).symm.trans
    ((congrArg (Deformation.Maps.BundleCycles.deformationSpecialMap I J f hIJ)
      ((SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).apply_symm_apply x)).trans hx)

/-- The actual inclusion of the normal cone of a closed support. -/
def closedSupportNormalConeInclusion (I P : Ideal R) :
    Normal.Cone.BundleCycles.affineNormalCone (I.map (Ideal.Quotient.mk P)) ⟶ Normal.Cone.BundleCycles.affineNormalCone I :=
  Spec.map (CommRingCat.ofHom
    (Deformation.Maps.BundleCycles.normalConeMap I _ (Ideal.Quotient.mk P) (fun _ hp => Ideal.mem_map_of_mem _ hp)))

instance closedSupportNormalConeInclusion_isClosedImmersion (I P : Ideal R) :
    IsClosedImmersion (closedSupportNormalConeInclusion I P) :=
  IsClosedImmersion.spec_of_surjective _
    (normalConeMap_surjective I _ (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective rfl _)

/-- The point embedding for the genuine closed normal-cone inclusion. -/
def closedSupportNormalConePointEmbedding (I P : Ideal R) :
    Normal.Cone.BundleCycles.affineNormalCone (I.map (Ideal.Quotient.mk P)) ↪ Normal.Cone.BundleCycles.affineNormalCone I :=
  ⟨closedSupportNormalConeInclusion I P,
    (closedSupportNormalConeInclusion I P).isClosedEmbedding.injective⟩

variable [IsNoetherianRing R]

/-- Specialization of the integral affine cycle defined by a prime ideal. -/
def affinePrimeSpecialization (I : Ideal R) (P : PrimeSpectrum R) : Normal.Cone.BundleCycles.affineNormalCone I →₀ ℤ :=
  Finsupp.embDomain (closedSupportNormalConePointEmbedding I P.asIdeal)
    (Affine.Specialization.BundleCycles.affineSpecializationCycle (I.map (Ideal.Quotient.mk P.asIdeal)))

theorem affinePrimeSpecialization_at_support (I : Ideal R) (P : PrimeSpectrum R)
    (x : Normal.Cone.BundleCycles.affineNormalCone (I.map (Ideal.Quotient.mk P.asIdeal))) :
    affinePrimeSpecialization I P (closedSupportNormalConeInclusion I P.asIdeal x) =
      Affine.Specialization.BundleCycles.affineSpecializationCycle (I.map (Ideal.Quotient.mk P.asIdeal)) x :=
  Finsupp.embDomain_apply_self _ _ _

/-- Rational coefficients on the same genuine specialization cycle. -/
def affinePrimeSpecializationQ (I : Ideal R) (P : PrimeSpectrum R) : Normal.Cone.BundleCycles.affineNormalCone I →₀ ℚ :=
  (affinePrimeSpecialization I P).mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero

/-- Specialization on finite rational affine cycles, before passage to Chow groups. -/
def affineCycleSpecialization (I : Ideal R) :
    (PrimeSpectrum R →₀ ℚ) →ₗ[ℚ] (Normal.Cone.BundleCycles.affineNormalCone I →₀ ℚ) :=
  Finsupp.linearCombination ℚ (affinePrimeSpecializationQ I)

@[simp]
theorem affineCycleSpecialization_single (I : Ideal R) (P : PrimeSpectrum R) (q : ℚ) :
    affineCycleSpecialization I (Finsupp.single P q) = q • affinePrimeSpecializationQ I P :=
  Finsupp.linearCombination_single ℚ q P

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CycleSpecialization.BundleCycles
