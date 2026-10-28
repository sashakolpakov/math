import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.RegularFactorization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.Diagonal
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationExact
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationLength

/-! # Power Exact -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PowerExact.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the branch product is a uniformizer power

Cleared factorizations of a and b identify the actual localized
product ideal with (t^(m+n)). Injectivity of the unit numerators
then proves that this power annihilates the original branch image.
-/

variable {R : Type*} [CommRing R]

theorem branchFactor_product_identity (a b t u s v w : R) (m n : ℕ)
    (ha : s * a = u * t ^ m) (hb : w * b = v * t ^ n) :
    (s * w) * (a * b) = (u * v) * t ^ (m + n) := by
  calc
    (s * w) * (a * b) = (s * a) * (w * b) := by ring
    _ = (u * v) * t ^ (m + n) := by rw [ha, hb, pow_add]; ring

theorem branchUniformizerPower_annihilates (a b t u s v w : R) (m n : ℕ)
    (P : Ideal R) [P.IsPrime] (hu : u ∉ P) (hv : v ∉ P)
    (ha : s * a = u * t ^ m) (hb : w * b = v * t ^ n) :
    ∀ z : PeriodicComplex.BundleCycles.productBranchModule a b P, t ^ (m + n) • z = 0 := by
  intro z
  apply PeriodicComplex.BundleCycles.productBranch_denominator_injective a b P (u * v) (P.primeCompl.mul_mem hu hv)
  change (u * v) • (t ^ (m + n) • z) = (u * v) • 0
  calc
    (u * v) • (t ^ (m + n) • z) = ((s * w) * (a * b)) • z :=
      (mul_smul (u * v) (t ^ (m + n)) z).symm.trans
        (congrArg (fun c : R => c • z) (branchFactor_product_identity a b t u s v w m n ha hb).symm)
    _ = (s * w) • ((a * b) • z) := mul_smul _ _ _
    _ = 0 := by rw [Diagonal.BundleCycles.productBranch_annihilated, smul_zero]
    _ = (u * v) • 0 := (smul_zero _).symm

theorem branchUniformizer_localized_product_ideal (a b t u s v w : R) (m n : ℕ)
    (P : Ideal R) [P.IsPrime] (hu : u ∉ P) (hs : s ∉ P) (hv : v ∉ P) (hw : w ∉ P)
    (ha : s * a = u * t ^ m) (hb : w * b = v * t ^ n) :
    (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) =
      Ideal.span {(algebraMap R (Localization P.primeCompl) t) ^ (m + n)} := by
  let A := Localization P.primeCompl
  let f := algebraMap R A
  have hsw : IsUnit (f (s * w)) := IsLocalization.map_units A ⟨s * w, P.primeCompl.mul_mem hs hw⟩
  have huv : IsUnit (f (u * v)) := IsLocalization.map_units A ⟨u * v, P.primeCompl.mul_mem hu hv⟩
  have he : f (s * w) * f (a * b) = f (u * v) * (f t) ^ (m + n) := by
    rw [← map_mul, branchFactor_product_identity a b t u s v w m n ha hb, map_mul, map_pow]
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {f (a * b)} = Ideal.span {(f t) ^ (m + n)}
  calc
    Ideal.span {f (a * b)} = Ideal.span {f (s * w) * f (a * b)} :=
      (Ideal.span_singleton_mul_left_unit hsw _).symm
    _ = Ideal.span {f (u * v) * (f t) ^ (m + n)} := congrArg (fun z : A => Ideal.span {z}) he
    _ = Ideal.span {(f t) ^ (m + n)} := Ideal.span_singleton_mul_left_unit huv _

end

/-!
# LineBundleCycles: actual local exactness for complementary uniformizer powers

The localized branch is identified with the quotient by its computed
product ideal. Once that ideal is (t^N), complementary powers are the
two factors of this actual quotient, whose multiplication complex is exact.
-/

theorem equationEndomorphism_restrictScalars
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (x : R) :
    (MultiplicationSequence.BundleCycles.equationEndomorphism (algebraMap R A x) M).restrictScalars R = MultiplicationSequence.BundleCycles.equationEndomorphism x M := by
  apply LinearMap.ext
  intro m
  exact IsScalarTower.algebraMap_smul A x m

variable {R : Type*} [CommRing R]

def branchQuotientLocalEquiv (a b : R) (P : Ideal R) [P.IsPrime]
    (J : Ideal (Localization P.primeCompl))
    (hJ : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) = J) :
    LocalizedModule P.primeCompl (PeriodicComplex.BundleCycles.productBranchModule a b P) ≃ₗ[R] (Localization P.primeCompl) ⧸ J :=
  (PeriodicComplex.BundleCycles.productBranchLocalEquiv a b P).trans
    (((LocalizedEquationLength.BundleCycles.localizedIdealQuotientEquiv P.primeCompl (Ideal.span {a * b})).trans
      (Submodule.quotEquivOfEq _ _ hJ)).restrictScalars R)

theorem branchPower_local_exact [IsDomain R]
    (a b t : R) (N i j : ℕ) (hij : i + j = N) (P : Ideal R) [P.IsPrime]
    (ht : algebraMap R (Localization P.primeCompl) t ≠ 0)
    (hI : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) =
      Ideal.span {(algebraMap R (Localization P.primeCompl) t) ^ N}) :
    Function.Exact
      (MultiplicationSequence.BundleCycles.equationEndomorphism (t ^ i) (LocalizedModule P.primeCompl (PeriodicComplex.BundleCycles.productBranchModule a b P)))
      (MultiplicationSequence.BundleCycles.equationEndomorphism (t ^ j) (LocalizedModule P.primeCompl (PeriodicComplex.BundleCycles.productBranchModule a b P))) := by
  let A := Localization P.primeCompl
  let α := algebraMap R A (t ^ i)
  let β := algebraMap R A (t ^ j)
  have hprod : α * β = (algebraMap R A t) ^ N := by
    dsimp only [α, β]
    rw [map_pow, map_pow, ← pow_add, hij]
  have hβ : β ≠ 0 := by
    dsimp only [β]
    rw [map_pow]
    exact pow_ne_zero j ht
  have hJ : (Ideal.span {a * b}).map (algebraMap R A) = Ideal.span {α * β} :=
    hI.trans (congrArg (fun z : A => Ideal.span {z}) hprod.symm)
  let e : LocalizedModule P.primeCompl (PeriodicComplex.BundleCycles.productBranchModule a b P) ≃ₗ[R]
      ProductPeriodicComplex.BundleCycles.productEquationQuotient α β := branchQuotientLocalEquiv a b P _ hJ
  have hex : Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism (t ^ i) (ProductPeriodicComplex.BundleCycles.productEquationQuotient α β))
      (MultiplicationSequence.BundleCycles.equationEndomorphism (t ^ j) (ProductPeriodicComplex.BundleCycles.productEquationQuotient α β)) := by
    rw [← equationEndomorphism_restrictScalars (A := A) (t ^ i),
      ← equationEndomorphism_restrictScalars (A := A) (t ^ j)]
    exact ProductPeriodicComplex.BundleCycles.productEquation_exact α β hβ
  exact LocalizedEquationExact.BundleCycles.equationEndomorphism_exact_equiv (t ^ i) (t ^ j) e.symm hex

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PowerExact.BundleCycles
