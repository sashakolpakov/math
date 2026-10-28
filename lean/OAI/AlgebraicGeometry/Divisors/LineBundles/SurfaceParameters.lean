import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfacePrimeFactors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Surface Parameters -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceParameters.BundleCycles

noncomputable section

/-!
# LineBundleCycles: proper parameters on a local surface

When (a,b) has maximal radical in a two-dimensional Noetherian local
ring, a is outside every prime minimal over (b). Krull's principal
ideal theorem rules out a common minimal component. This supplies
the actual injectivity on each prime support used in intersection lengths.
-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem surfaceParameter_not_mem_minimal (a b : R)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R)
    (P : Ideal R) (hP : P ∈ (Ideal.span {b}).minimalPrimes) : a ∉ P := by
  let : P.IsPrime := hP.isPrime
  intro haP
  have hbP : b ∈ P := hP.le (Ideal.subset_span (Set.mem_singleton b))
  have hle : Ideal.span {a, b} ≤ P := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact haP
    · exact (Set.mem_singleton_iff.mp hx) ▸ hbP
  have hmP : IsLocalRing.maximalIdeal R ≤ P := by
    rw [← hab]
    exact (Ideal.radical_mono hle).trans_eq hP.isPrime.radical
  have hPe : P = IsLocalRing.maximalIdeal R :=
    le_antisymm (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hmP
  have hh : P.height ≤ (1 : ℕ∞) :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {b}) P hP
  have hh' : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) ≤ 1 :=
    WithBot.coe_le_coe.mpr (hPe ▸ hh)
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim] at hh'
  exact (by norm_num : ¬ (2 : WithBot ℕ∞) ≤ 1) hh'

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceParameters.BundleCycles
