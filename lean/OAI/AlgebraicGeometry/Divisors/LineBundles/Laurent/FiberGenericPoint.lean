import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.DivisorPrimes
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Fiber Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.FiberGenericPoint.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the actual affine punctured-line projection -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

def laurentProjection : Spec (CommRingCat.of (LaurentPolynomial R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R)))

theorem laurentConstant_injective : Function.Injective (algebraMap R (LaurentPolynomial R)) := by
  intro a b h
  have hc := congrArg (LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ)) h
  change LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ) (LaurentPolynomial.C a) =
    LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ) (LaurentPolynomial.C b) at hc
  simpa only [LaurentPolynomial.eval₂_C, RingHom.id_apply] using hc

instance laurentProjection_flat : Flat (laurentProjection R) := by
  let : Module.Flat R (LaurentPolynomial R) := Module.Flat.of_free
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

instance laurent_noetherian [IsNoetherianRing R] : IsNoetherianRing (LaurentPolynomial R) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : Polynomial R))
    (LaurentPolynomial R) inferInstance

variable [IsDomain R]

theorem laurentProjection_genericPoint :
    laurentProjection R (genericPoint (Spec (CommRingCat.of (LaurentPolynomial R)))) =
      genericPoint (Spec (CommRingCat.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap R (LaurentPolynomial R))).mp
    (laurentConstant_injective R)

def laurentFunctionFieldMap : (Spec (CommRingCat.of R)).functionField ⟶
    (Spec (CommRingCat.of (LaurentPolynomial R))).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (laurentProjection R) (laurentProjection_genericPoint R)

def laurentPrimePoint (p : Spec (CommRingCat.of R)) : Spec (CommRingCat.of (LaurentPolynomial R)) :=
  ⟨PrimeExtension.BundleCycles.laurentPrimeExtension p.asIdeal, @PrimeExtension.BundleCycles.laurentPrimeExtension_isPrime R _ p.asIdeal (show PrimeSpectrum R from p).isPrime⟩

omit [IsDomain R] in
theorem laurentPrimePoint_projection (p : Spec (CommRingCat.of R)) :
    laurentProjection R (laurentPrimePoint R p) = p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  exact PrimeSpectrum.ext (PrimeExtension.BundleCycles.laurentPrimeExtension_under p.asIdeal)

omit [IsDomain R] in
theorem laurentPrimePoint_injective : Function.Injective (laurentPrimePoint R) :=
  Function.LeftInverse.injective (laurentPrimePoint_projection R)

omit [IsDomain R] in
theorem laurentPrimePoint_coheight [IsNoetherianRing R] (p : Spec (CommRingCat.of R)) :
    Order.coheight (laurentPrimePoint R p) = Order.coheight p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact PrimeExtension.BundleCycles.laurentPrimeExtension_height p.asIdeal

end

/-! # LineBundleCycles: the actual generic point in each punctured-line fiber -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (R : Type) [CommRing R]

theorem laurentProjection_surjective : Function.Surjective (laurentProjection R) :=
  Function.HasRightInverse.surjective ⟨laurentPrimePoint R, laurentPrimePoint_projection R⟩

theorem laurentPrimePoint_specializes (P : Spec (CommRingCat.of (LaurentPolynomial R))) :
    laurentPrimePoint R (laurentProjection R P) ⤳ P := by
  apply (PrimeSpectrum.le_iff_specializes _ _).mp
  change PrimeExtension.BundleCycles.laurentPrimeExtension (P.asIdeal.under R) ≤ P.asIdeal
  rw [PrimeExtension.BundleCycles.laurentPrimeExtension_eq_map]
  exact Ideal.map_comap_le

theorem laurentPrimePoint_specializes_fiber (p : Spec (CommRingCat.of R))
    (P : Spec (CommRingCat.of (LaurentPolynomial R))) (hP : laurentProjection R P = p) :
    laurentPrimePoint R p ⤳ P := by
  rw [← hP]
  exact laurentPrimePoint_specializes R P

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.FiberGenericPoint.BundleCycles
