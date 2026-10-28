import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.FiberGenericPoint

/-! # Prime Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.PrimeNaturality.BundleCycles

noncomputable section

/-! # LineBundleCycles: Laurent prime extensions commute with actual coefficient maps -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S : Type} [CommRing R] [CommRing S]

theorem laurentPrimeExtension_mem_iff (p : Ideal R) (a : LaurentPolynomial R) :
    a ∈ PrimeExtension.BundleCycles.laurentPrimeExtension p ↔ ∀ n, a.coeff n ∈ p := by
  let q := AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk p)
  have hker : PrimeExtension.BundleCycles.laurentPrimeExtension p ≤ RingHom.ker q := by
    rw [PrimeExtension.BundleCycles.laurentPrimeExtension_eq_map, Ideal.map_le_iff_le_comap]
    intro r hr
    change q (LaurentPolynomial.C r) = 0
    change q (AddMonoidAlgebra.single 0 r) = 0
    rw [AddMonoidAlgebra.mapRingHom_single, Ideal.Quotient.eq_zero_iff_mem.mpr hr,
      AddMonoidAlgebra.single_zero]
  constructor
  · intro ha n
    have hq : q a = 0 := hker ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (AddMonoidAlgebra.coeff_mapRingHom (Ideal.Quotient.mk p) a n).symm.trans
      (congrArg (fun b : LaurentPolynomial (R ⧸ p) => b.coeff n) hq)
  · intro ha
    rw [← AddMonoidAlgebra.sum_coeff_single a]
    apply Ideal.sum_mem
    intro n hn
    have hc : LaurentPolynomial.C (a.coeff n) ∈ PrimeExtension.BundleCycles.laurentPrimeExtension p := by
      rw [PrimeExtension.BundleCycles.laurentPrimeExtension_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap R (LaurentPolynomial R)) (ha n)
    rw [LaurentPolynomial.single_eq_C_mul_T]
    exact (PrimeExtension.BundleCycles.laurentPrimeExtension p).mul_mem_right (LaurentPolynomial.T n) hc

theorem laurentPrimeExtension_comap (f : R →+* S) (p : Ideal S) :
    (PrimeExtension.BundleCycles.laurentPrimeExtension p).comap (AddMonoidAlgebra.mapRingHom ℤ f) =
      PrimeExtension.BundleCycles.laurentPrimeExtension (p.comap f) := by
  ext a
  simp only [Ideal.mem_comap, laurentPrimeExtension_mem_iff, AddMonoidAlgebra.coeff_mapRingHom]

theorem laurentPrimePoint_map (f : R →+* S) (p : Spec (CommRingCat.of S)) :
    Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f)) (FiberGenericPoint.BundleCycles.laurentPrimePoint S p) =
      FiberGenericPoint.BundleCycles.laurentPrimePoint R (Spec.map (CommRingCat.ofHom f) p) :=
  PrimeSpectrum.ext (laurentPrimeExtension_comap f p.asIdeal)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.PrimeNaturality.BundleCycles
