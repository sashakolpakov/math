import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! # Closed Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport.BundleCycles

noncomputable section

/-!
# LineBundleCycles: deformation of closed cycle supports

A surjective base-ring homomorphism induces a surjection on extended Rees
algebras for the image ideal. Its spectrum is therefore an actual closed
immersion. In particular the deformation of a closed integral cycle support
embeds into the ambient deformation, rather than being supplied as abstract
data.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped BigOperators

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Surjectivity on base rings gives surjectivity on the actual extended
Rees algebras, with the ideal replaced by its image. -/
theorem deformationMap_surjective (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : Function.Surjective f) (hJ : I.map f = J) (hIJ : I ≤ J.comap f) :
    Function.Surjective (Maps.BundleCycles.deformationMap I J f hIJ) := by
  classical
  intro p
  have hm (n : ℤ) : Iff.BundleCycles.deformationMonomial J n (p.val.coeff n) (p.property n) ∈
      (Maps.BundleCycles.deformationMap I J f hIJ).rangeS := by
    have hc : p.val.coeff n ∈ (I ^ (-n).toNat).map f := by
      rw [Ideal.map_pow, hJ]
      exact p.property n
    obtain ⟨r, hr, he⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hc
    refine ⟨Iff.BundleCycles.deformationMonomial I n r hr, Subtype.ext ?_⟩
    change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single n r) =
      AddMonoidAlgebra.single n (p.val.coeff n)
    rw [AddMonoidAlgebra.mapRingHom_single, he]
  have he : p = ∑ n ∈ p.val.coeff.support, Iff.BundleCycles.deformationMonomial J n (p.val.coeff n) (p.property n) := by
    apply Subtype.ext
    change p.val = (Iff.BundleCycles.deformationAlgebra J).val
      (∑ n ∈ p.val.coeff.support, Iff.BundleCycles.deformationMonomial J n (p.val.coeff n) (p.property n))
    rw [map_sum]
    exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
  have hp : p ∈ (Maps.BundleCycles.deformationMap I J f hIJ).rangeS := by
    rw [he]
    exact Subsemiring.sum_mem _ fun n _ => hm n
  exact hp

/-- The actual spectrum of an affine deformation algebra. -/
def affineDeformation (I : Ideal R) : Scheme := Spec (CommRingCat.of (Iff.BundleCycles.deformationAlgebra I))

/-- Deformation of the closed subscheme cut out by P, along the restricted center. -/
def closedSupportDeformation (I P : Ideal R) : Scheme :=
  affineDeformation (I.map (Ideal.Quotient.mk P))

/-- The quotient on coefficients restricts to the deformation algebra. -/
def closedSupportDeformationRingMap (I P : Ideal R) :
    Iff.BundleCycles.deformationAlgebra I →+* Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk P)) :=
  Maps.BundleCycles.deformationMap I _ (Ideal.Quotient.mk P) (fun _ hr => Ideal.mem_map_of_mem _ hr)

theorem closedSupportDeformationRingMap_surjective (I P : Ideal R) :
    Function.Surjective (closedSupportDeformationRingMap I P) :=
  deformationMap_surjective I _ (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective rfl _

/-- The deformation of a closed support is a closed subscheme of the ambient deformation. -/
def closedSupportDeformationInclusion (I P : Ideal R) :
    closedSupportDeformation I P ⟶ affineDeformation I :=
  Spec.map (CommRingCat.ofHom (closedSupportDeformationRingMap I P))

instance closedSupportDeformationInclusion_isClosedImmersion (I P : Ideal R) :
    IsClosedImmersion (closedSupportDeformationInclusion I P) :=
  IsClosedImmersion.spec_of_surjective _ (closedSupportDeformationRingMap_surjective I P)

/-- Its defining ideal consists exactly of Laurent polynomials with all
coefficients in the original support ideal P. -/
theorem closedSupportDeformationRingMap_eq_zero_iff (I P : Ideal R) (p : Iff.BundleCycles.deformationAlgebra I) :
    closedSupportDeformationRingMap I P p = 0 ↔ ∀ n, p.val.coeff n ∈ P := by
  constructor
  · intro h n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrArg (fun q : Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk P)) => q.val.coeff n) h
  · intro h
    apply Subtype.ext
    ext n
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h n)

instance affineDeformation_isIntegral (I : Ideal R) [IsDomain R] : IsIntegral (affineDeformation I) := by
  exact inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Iff.BundleCycles.deformationAlgebra I))))

instance affineDeformation_isNoetherian (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.IsNoetherian (affineDeformation I) := by
  exact inferInstanceAs (AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of (Iff.BundleCycles.deformationAlgebra I))))

instance closedSupportDeformation_isIntegral (I P : Ideal R) [P.IsPrime] :
    IsIntegral (closedSupportDeformation I P) := by
  exact affineDeformation_isIntegral (I.map (Ideal.Quotient.mk P))

instance closedSupportDeformation_isNoetherian (I P : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.IsNoetherian (closedSupportDeformation I P) :=
  affineDeformation_isNoetherian (I.map (Ideal.Quotient.mk P))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport.BundleCycles
