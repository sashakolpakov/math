import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual affine-line projection and its extended prime points -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Polynomial

variable (R : Type) [CommRing R]

def polynomialProjection : Spec (.of R[X]) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R[X]))

instance polynomialProjection_flat : Flat (polynomialProjection R) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr Module.Flat.of_free)

def polynomialPrimePoint (p : Spec (.of R)) : Spec (.of R[X]) :=
  ⟨p.asIdeal.map C, by
    let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
    infer_instance⟩

theorem polynomialPrimePoint_projection (p : Spec (.of R)) :
    polynomialProjection R (polynomialPrimePoint R p) = p :=
  PrimeSpectrum.ext (PrimeExtension.BundleCycles.polynomialPrimeExtension_comap p.asIdeal)

theorem polynomialPrimePoint_injective : Function.Injective (polynomialPrimePoint R) :=
  Function.LeftInverse.injective (polynomialPrimePoint_projection R)

theorem polynomialPrimePoint_coheight [IsNoetherianRing R] (p : Spec (.of R)) :
    Order.coheight (polynomialPrimePoint R p) = Order.coheight p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact PrimeExtension.BundleCycles.polynomialPrimeExtension_height p.asIdeal

theorem polynomialPrimePoint_specializes (P : Spec (.of R[X])) :
    polynomialPrimePoint R (polynomialProjection R P) ⤳ P := by
  apply (PrimeSpectrum.le_iff_specializes _ _).mp
  exact Ideal.map_comap_le

variable [IsDomain R]

theorem polynomialProjection_genericPoint :
    polynomialProjection R (genericPoint (Spec (.of R[X]))) = genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap R R[X])).mp C_injective

def polynomialFunctionFieldMap : (Spec (.of R)).functionField ⟶ (Spec (.of R[X])).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (polynomialProjection R) (polynomialProjection_genericPoint R)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection.BundleCycles
