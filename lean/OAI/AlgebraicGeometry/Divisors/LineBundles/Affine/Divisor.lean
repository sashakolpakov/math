import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ImageRegularFunction
import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceGeometricIntersection

/-! # Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Divisor.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the prime-quotient functions are actual restrictions of ambient equations

The canonical affine section corresponding to a ring element pulls back
through the quotient map to its quotient class. Transport to the actual
reduced image then agrees with supportRegularFunction, also for ratios.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

local instance affinePrimeRestriction_fieldAlgebra (S : Type) [CommRing S] [IsDomain S] :
    Algebra S (Spec (.of S)).functionField :=
  (StructureSheaf.toStalk S (genericPoint (Spec (.of S)))).hom.toAlgebra

local instance affinePrimeRestriction_isFractionRing (S : Type) [CommRing S] [IsDomain S] :
    IsFractionRing S (Spec (.of S)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of S)

variable (R : Type) [CommRing R] (P : Ideal R) [P.IsPrime]

def affineAmbientSection (a : R) : Γ(Spec (CommRingCat.of R), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv a

theorem affinePrimeQuotient_regularFunction (a : R) :
    RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of (R ⧸ P)))
      ((PrimeSupport.BundleCycles.affinePrimeQuotientMap R P).appTop (affineAmbientSection R a)) =
        LocalDivisor.BundleCycles.affineGenericFieldIso (R ⧸ P) (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P a)) := by
  have ha : (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P).appTop (affineAmbientSection R a) =
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ P))).inv (Ideal.Quotient.mk P a) :=
    (congrArg (fun j : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of (R ⧸ P)), ⊤) => j a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk P)))).symm
  rw [ha, AlgEquiv.commutes]
  rfl

theorem affinePrimeLocalFunction_regular (a : R) :
    LocalDivisor.BundleCycles.affinePrimeLocalFunction R P (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P a)) =
      Principal.CartierCycle.BundleCycles.supportRegularFunction (affineAmbientSection R a) (CycleClass.Geometric.StratumClosure.integralImageClosure (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P)) := by
  unfold LocalDivisor.BundleCycles.affinePrimeLocalFunction
  rw [← affinePrimeQuotient_regularFunction, Closed.ImageRegularFunction.BundleCycles.integralClosedImageFunction_regular]

theorem affinePrimeLocalFunction_ratio (a c : R) :
    LocalDivisor.BundleCycles.affinePrimeLocalFunction R P (SurfaceRationalOrderIntersection.BundleCycles.primeSupportRationalFunction a c P) =
      Principal.CartierCycle.BundleCycles.supportRegularFunction (affineAmbientSection R a) (CycleClass.Geometric.StratumClosure.integralImageClosure (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P)) /
        Principal.CartierCycle.BundleCycles.supportRegularFunction (affineAmbientSection R c) (CycleClass.Geometric.StratumClosure.integralImageClosure (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P)) := by
  have hd (g h : FractionRing (R ⧸ P)) :
      LocalDivisor.BundleCycles.affinePrimeLocalFunction R P (g / h) = LocalDivisor.BundleCycles.affinePrimeLocalFunction R P g / LocalDivisor.BundleCycles.affinePrimeLocalFunction R P h := by
    unfold LocalDivisor.BundleCycles.affinePrimeLocalFunction Integral.ClosedImage.BundleCycles.integralClosedImageFunction
    rw [map_div₀, map_div₀]
  rw [SurfaceRationalOrderIntersection.BundleCycles.primeSupportRationalFunction, hd, affinePrimeLocalFunction_regular, affinePrimeLocalFunction_regular]

end

section

/-!
# LineBundleCycles: native affine divisor coefficients are the actual prime equation multiplicities

The affine germ is the canonical localization map. Its actual stalk
isomorphism identifies the quotient length defining Scheme.ord with
the quotient length R_P/bR_P used in the geometric intersection sum.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]

local instance affineDivisorMultiplicity_stalkAlgebra (x : Spec (CommRingCat.of R)) :
    Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x

theorem affineRegularDivisor_coefficient (b : R) (hb : b ≠ 0)
    (x : Spec (CommRingCat.of R)) (hx : coheight x = 1) :
    (Spec (CommRingCat.of R)).ord
      (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (affineAmbientSection R b)) x =
        (LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b x.asIdeal (show x.asIdeal.IsPrime from x.isPrime) : ℤ) := by
  let : x.asIdeal.IsPrime := (show PrimeSpectrum R from x).isPrime
  let e : Localization.AtPrime x.asIdeal ≃ₐ[R] (Spec (CommRingCat.of R)).presheaf.stalk x :=
    StructureSheaf.stalkIso R (show PrimeSpectrum R from x)
  have hsec : affineAmbientSection R b ≠ 0 :=
    (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).injective).mpr hb
  have hs := RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length (Spec (CommRingCat.of R))
    (affineAmbientSection R b) hsec x hx
  have hg : (Spec (CommRingCat.of R)).presheaf.germ ⊤ x (by trivial) (affineAmbientSection R b) =
      algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk x) b := rfl
  have he : Ring.ord ((Spec (CommRingCat.of R)).presheaf.stalk x)
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ x (by trivial) (affineAmbientSection R b)) =
        Ring.ord (Localization.AtPrime x.asIdeal) (algebraMap R (Localization.AtPrime x.asIdeal) b) := by
    rw [hg, ← e.commutes b]
    exact DivisorRestriction.BundleCycles.ringOrder_equiv e.toRingEquiv _
  change (Spec (CommRingCat.of R)).ord
    (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (affineAmbientSection R b)) x =
      ((Ring.ord ((Spec (CommRingCat.of R)).presheaf.stalk x)
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ x (by trivial) (affineAmbientSection R b))).toNat : ℤ) at hs
  rw [he] at hs
  exact hs

end

section

/-!
# LineBundleCycles: the actual prime supports of an affine regular divisor

For a nonzero equation on an integral Noetherian affine scheme, the
divisor points are its minimal prime components. Outside those components
the native order is zero. This identifies the support used by the finite
geometric intersection formula with the actual principal divisor.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem affineMinimalPrime_coheight (b : R) (hb : b ≠ 0)
    (P : Ideal R) (hP : P ∈ (Ideal.span {b}).minimalPrimes) :
    letI : P.IsPrime := hP.isPrime
    coheight (PrimeSupport.BundleCycles.affinePrimePoint R P) = 1 := by
  let : P.IsPrime := hP.isPrime
  rw [← idealHeight_eq_coheight]
  apply le_antisymm
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {b}) P hP
  · exact (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hb)).trans (Ideal.height_mono hP.le)

theorem affineDivisorPoint_mem_minimal (b : R) (hb : b ≠ 0)
    (x : Spec (CommRingCat.of R)) (hx : coheight x = 1) (hbx : b ∈ x.asIdeal) :
    x.asIdeal ∈ (Ideal.span {b}).minimalPrimes := by
  let : x.asIdeal.IsPrime := (show PrimeSpectrum R from x).isPrime
  have hh : x.asIdeal.height = 1 := (idealHeight_eq_coheight (CommRingCat.of R) x).trans hx
  exact Ideal.mem_minimalPrimes_of_height_le
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbx))
    (hh ▸ Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb))

theorem affineRegularDivisor_eq_zero_of_not_mem (b : R) (x : Spec (CommRingCat.of R))
    (hb : b ∉ x.asIdeal) :
    (Spec (CommRingCat.of R)).ord
      (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (affineAmbientSection R b)) x = 0 := by
  have hu : x ∈ (Spec (CommRingCat.of R)).basicOpen (affineAmbientSection R b) := by
    unfold affineAmbientSection
    rw [basicOpen_eq_of_affine]
    exact hb
  exact RegularDivisor.BundleCycles.regularFunctionDivisor_eq_zero_of_isUnit_germ (Spec (CommRingCat.of R)) (affineAmbientSection R b) x
    ((Scheme.mem_basicOpen (Spec (CommRingCat.of R)) (affineAmbientSection R b) x (by trivial)).mp hu)

theorem affineRegularDivisor_eq_zero_of_not_minimal (b : R) (hb : b ≠ 0)
    (x : Spec (CommRingCat.of R)) (hx : x.asIdeal ∉ (Ideal.span {b}).minimalPrimes) :
    (Spec (CommRingCat.of R)).ord
      (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (affineAmbientSection R b)) x = 0 := by
  by_cases hc : coheight x = 1
  · exact affineRegularDivisor_eq_zero_of_not_mem b x
      (fun h => hx (affineDivisorPoint_mem_minimal b hb x hc h))
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hc _

end

/-!
# LineBundleCycles: the complete native affine divisor as its finite minimal-prime sum

The indexing set is the actual finite set of minimal primes of the
equation. Their points are distinct, and the coefficients are the proved
local equation lengths. All other native divisor coefficients vanish.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order
open scoped Classical

variable (R : Type) [CommRing R] [IsNoetherianRing R]

abbrev affineDivisorPrimeIndex (b : R) := {P : Ideal R // P ∈ (Ideal.span {b}).minimalPrimes}

instance affineDivisorPrimeIndex_fintype (b : R) : Fintype (affineDivisorPrimeIndex R b) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).fintype

def affineDivisorPrimePoint (b : R) (P : affineDivisorPrimeIndex R b) : Spec (CommRingCat.of R) :=
  ⟨P.val, P.property.isPrime⟩

omit [IsNoetherianRing R] in
theorem affineDivisorPrimePoint_injective (b : R) : Function.Injective (affineDivisorPrimePoint R b) := by
  intro P Q h
  exact Subtype.ext (congrArg PrimeSpectrum.asIdeal h)

variable [IsDomain R]

theorem affineRegularDivisor_eq_prime_sum (b : R) (hb : b ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of R))
      (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (affineAmbientSection R b)) =
      ∑ P : affineDivisorPrimeIndex R b, Finsupp.single (affineDivisorPrimePoint R b P)
        (LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b P.val P.property.isPrime : ℚ) := by
  ext x
  rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Finsupp.finsetSum_apply]
  by_cases hx : x.asIdeal ∈ (Ideal.span {b}).minimalPrimes
  · let P : affineDivisorPrimeIndex R b := ⟨x.asIdeal, hx⟩
    have he : affineDivisorPrimePoint R b P = x := rfl
    have hc : coheight (affineDivisorPrimePoint R b P) = 1 := affineMinimalPrime_coheight b hb _ hx
    rw [← he, affineRegularDivisor_coefficient R b hb (affineDivisorPrimePoint R b P) hc]
    rw [Finset.sum_eq_single P]
    · rw [Finsupp.single_eq_same, Int.cast_natCast]
      rfl
    · intro Q _ hQP
      exact Finsupp.single_eq_of_ne (fun h => hQP (affineDivisorPrimePoint_injective R b h.symm))
    · simp
  · rw [affineRegularDivisor_eq_zero_of_not_minimal b hb x hx, Int.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro P _
    apply Finsupp.single_eq_of_ne
    intro he
    have hp : x.asIdeal = P.val := congrArg PrimeSpectrum.asIdeal he
    exact hx (hp.symm ▸ P.property)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Divisor.BundleCycles
