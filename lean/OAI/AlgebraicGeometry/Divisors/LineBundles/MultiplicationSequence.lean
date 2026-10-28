import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.RingTheory.Length

/-! # Multiplication Sequence -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.MultiplicationSequence.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the multiplication diagram for a module and a submodule

Multiplication by an equation preserves every submodule and commutes
with the actual quotient map. Its kernel and cokernel maps, and the
snake connecting map, are constructed from this diagram. They supply
the local algebra for comparing successive divisor multiplicities.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def equationEndomorphism (a : R) (N : Type*) [AddCommGroup N] [Module R N] : N →ₗ[R] N :=
  a • LinearMap.id

abbrev equationKernel (a : R) (N : Type*) [AddCommGroup N] [Module R N] :=
  (equationEndomorphism a N).ker

abbrev equationCokernel (a : R) (N : Type*) [AddCommGroup N] [Module R N] :=
  N ⧸ (equationEndomorphism a N).range

variable (a : R) (P : Submodule R M)

theorem equationEndomorphism_subtype :
    P.subtype.comp (equationEndomorphism a P) = (equationEndomorphism a M).comp P.subtype := rfl

theorem equationEndomorphism_quotient :
    P.mkQ.comp (equationEndomorphism a M) = (equationEndomorphism a (M ⧸ P)).comp P.mkQ := by
  ext x
  exact P.mkQ.map_smul a x

def equationKernelInclusion : equationKernel a P →ₗ[R] equationKernel a M :=
  LinearMap.codRestrict _ (P.subtype.comp (equationKernel a P).subtype) (fun x => by
    change a • x.1.1 = 0
    exact congrArg Subtype.val x.2)

def equationKernelQuotient : equationKernel a M →ₗ[R] equationKernel a (M ⧸ P) :=
  LinearMap.codRestrict _ (P.mkQ.comp (equationKernel a M).subtype) (fun x => by
    change a • P.mkQ x.1 = 0
    exact (P.mkQ.map_smul a x.1).symm.trans ((congrArg P.mkQ x.2).trans P.mkQ.map_zero))

theorem equationRange_subtype :
    (equationEndomorphism a P).range ≤ ((equationEndomorphism a M).range).comap P.subtype := by
  rintro x ⟨y, rfl⟩
  exact ⟨y.1, rfl⟩

theorem equationRange_quotient :
    (equationEndomorphism a M).range ≤ ((equationEndomorphism a (M ⧸ P)).range).comap P.mkQ := by
  rintro x ⟨y, rfl⟩
  exact ⟨P.mkQ y, (P.mkQ.map_smul a y).symm⟩

def equationCokernelInclusion : equationCokernel a P →ₗ[R] equationCokernel a M :=
  (equationEndomorphism a P).range.mapQ (equationEndomorphism a M).range P.subtype (equationRange_subtype a P)

def equationCokernelQuotient : equationCokernel a M →ₗ[R] equationCokernel a (M ⧸ P) :=
  (equationEndomorphism a M).range.mapQ (equationEndomorphism a (M ⧸ P)).range P.mkQ (equationRange_quotient a P)

/-- The actual connecting map of the multiplication diagram. -/
def equationSnakeBoundary : equationKernel a (M ⧸ P) →ₗ[R] equationCokernel a P :=
  SnakeLemma.δ' (equationEndomorphism a P) (equationEndomorphism a M) (equationEndomorphism a (M ⧸ P))
    P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P)
    P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P)
    (equationEndomorphism_subtype a P) (equationEndomorphism_quotient a P)
    (equationKernel a (M ⧸ P)).subtype (LinearMap.exact_subtype_ker_map (equationEndomorphism a (M ⧸ P)))
    (equationEndomorphism a P).range.mkQ (LinearMap.exact_map_mkQ_range (equationEndomorphism a P))
    P.mkQ_surjective P.subtype_injective

theorem equationKernelInclusion_injective : Function.Injective (equationKernelInclusion a P) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))

/-- Exactness of the kernel maps follows from actual quotient membership. -/
theorem equationKernel_exact : Function.Exact (equationKernelInclusion a P) (equationKernelQuotient a P) := by
  intro x
  constructor
  · intro hx
    have hp : x.1 ∈ P := (Submodule.Quotient.mk_eq_zero P).mp (congrArg Subtype.val hx)
    let y : equationKernel a P := ⟨⟨x.1, hp⟩, Subtype.ext x.2⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero P).mpr y.1.2

theorem equationCokernelQuotient_surjective : Function.Surjective (equationCokernelQuotient a P) := by
  intro x
  obtain ⟨q, rfl⟩ := (equationEndomorphism a (M ⧸ P)).range.mkQ_surjective x
  obtain ⟨y, rfl⟩ := P.mkQ_surjective q
  exact ⟨(equationEndomorphism a M).range.mkQ y, rfl⟩

/-- Exactness at the kernel on the quotient, from the actual snake boundary. -/
theorem equationSnake_kernel_exact : Function.Exact (equationKernelQuotient a P) (equationSnakeBoundary a P) :=
  SnakeLemma.exact_δ'_right
    (equationEndomorphism a P) (equationEndomorphism a M) (equationEndomorphism a (M ⧸ P))
    P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P)
    P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P)
    (equationEndomorphism_subtype a P) (equationEndomorphism_quotient a P)
    (equationKernel a M).subtype (LinearMap.exact_subtype_ker_map (equationEndomorphism a M))
    (equationKernel a (M ⧸ P)).subtype (LinearMap.exact_subtype_ker_map (equationEndomorphism a (M ⧸ P)))
    (equationEndomorphism a P).range.mkQ (LinearMap.exact_map_mkQ_range (equationEndomorphism a P))
    P.mkQ_surjective P.subtype_injective (equationKernelQuotient a P) rfl (Submodule.subtype_injective _)

/-- Exactness at the cokernel on the submodule, from the actual snake boundary. -/
theorem equationSnake_cokernel_exact : Function.Exact (equationSnakeBoundary a P) (equationCokernelInclusion a P) :=
  SnakeLemma.exact_δ'_left
    (equationEndomorphism a P) (equationEndomorphism a M) (equationEndomorphism a (M ⧸ P))
    P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P)
    P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P)
    (equationEndomorphism_subtype a P) (equationEndomorphism_quotient a P)
    (equationKernel a (M ⧸ P)).subtype (LinearMap.exact_subtype_ker_map (equationEndomorphism a (M ⧸ P)))
    (equationEndomorphism a P).range.mkQ (LinearMap.exact_map_mkQ_range (equationEndomorphism a P))
    (equationEndomorphism a M).range.mkQ (LinearMap.exact_map_mkQ_range (equationEndomorphism a M))
    P.mkQ_surjective P.subtype_injective (equationCokernelInclusion a P) rfl (Submodule.mkQ_surjective _)

/-- Exactness of the two cokernel maps, using surjectivity of the original quotient. -/
theorem equationCokernel_exact : Function.Exact (equationCokernelInclusion a P) (equationCokernelQuotient a P) := by
  apply ((LinearMap.exact_subtype_mkQ P).exact_mapQ_iff
    (equationRange_subtype a P) (equationRange_quotient a P)).mpr
  rintro x ⟨_, y, hy⟩
  obtain ⟨m, hm⟩ := P.mkQ_surjective y
  refine Submodule.mem_map.mpr ⟨equationEndomorphism a M m, ⟨m, rfl⟩, ?_⟩
  exact (P.mkQ.map_smul a m).trans ((congrArg (fun q => a • q) hm).trans hy)

end

/-!
# LineBundleCycles: the symmetric kernel term for two regular equations

The actual commuting multiplication diagram has rows
R --b--> R --> R/bR. Its snake boundary identifies the kernel of a on
R/bR with the kernel of b on R/aR when both equations act injectively
on R. These are the correction terms in successive intersection lengths.
-/

variable {R : Type*} [CommRing R] (a b : R)

theorem equationEndomorphisms_commute :
    (equationEndomorphism b R).comp (equationEndomorphism a R) =
      (equationEndomorphism a R).comp (equationEndomorphism b R) := by
  apply LinearMap.ext
  intro x
  change b * (a * x) = a * (b * x)
  exact mul_left_comm b a x

/-- The connecting map in the actual commuting two-equation diagram. -/
def twoEquationBoundary (hb : Function.Injective (equationEndomorphism b R)) :
    equationKernel a (equationCokernel b R) →ₗ[R] equationCokernel a R :=
  SnakeLemma.δ' (equationEndomorphism a R) (equationEndomorphism a R)
    (equationEndomorphism a (equationCokernel b R))
    (equationEndomorphism b R) (equationEndomorphism b R).range.mkQ
      (LinearMap.exact_map_mkQ_range (equationEndomorphism b R))
    (equationEndomorphism b R) (equationEndomorphism b R).range.mkQ
      (LinearMap.exact_map_mkQ_range (equationEndomorphism b R))
    (equationEndomorphisms_commute a b)
    (equationEndomorphism_quotient a (equationEndomorphism b R).range)
    (equationKernel a (equationCokernel b R)).subtype
      (LinearMap.exact_subtype_ker_map (equationEndomorphism a (equationCokernel b R)))
    (equationEndomorphism a R).range.mkQ (LinearMap.exact_map_mkQ_range (equationEndomorphism a R))
    (Submodule.mkQ_surjective _) hb

variable (hb : Function.Injective (equationEndomorphism b R))

theorem twoEquationBoundary_kernel_exact :
    Function.Exact (equationKernelQuotient a (equationEndomorphism b R).range) (twoEquationBoundary a b hb) :=
  SnakeLemma.exact_δ'_right
    (equationEndomorphism a R) (equationEndomorphism a R) (equationEndomorphism a (equationCokernel b R))
    (equationEndomorphism b R) (equationEndomorphism b R).range.mkQ
      (LinearMap.exact_map_mkQ_range (equationEndomorphism b R))
    (equationEndomorphism b R) (equationEndomorphism b R).range.mkQ
      (LinearMap.exact_map_mkQ_range (equationEndomorphism b R))
    (equationEndomorphisms_commute a b) (equationEndomorphism_quotient a (equationEndomorphism b R).range)
    (equationKernel a R).subtype (LinearMap.exact_subtype_ker_map (equationEndomorphism a R))
    (equationKernel a (equationCokernel b R)).subtype
      (LinearMap.exact_subtype_ker_map (equationEndomorphism a (equationCokernel b R)))
    (equationEndomorphism a R).range.mkQ (LinearMap.exact_map_mkQ_range (equationEndomorphism a R))
    (Submodule.mkQ_surjective _) hb (equationKernelQuotient a (equationEndomorphism b R).range) rfl
      (Submodule.subtype_injective _)

theorem twoEquationBoundary_range_exact :
    Function.Exact (twoEquationBoundary a b hb) (equationEndomorphism b (equationCokernel a R)) :=
  SnakeLemma.exact_δ'_left
    (equationEndomorphism a R) (equationEndomorphism a R) (equationEndomorphism a (equationCokernel b R))
    (equationEndomorphism b R) (equationEndomorphism b R).range.mkQ
      (LinearMap.exact_map_mkQ_range (equationEndomorphism b R))
    (equationEndomorphism b R) (equationEndomorphism b R).range.mkQ
      (LinearMap.exact_map_mkQ_range (equationEndomorphism b R))
    (equationEndomorphisms_commute a b) (equationEndomorphism_quotient a (equationEndomorphism b R).range)
    (equationKernel a (equationCokernel b R)).subtype
      (LinearMap.exact_subtype_ker_map (equationEndomorphism a (equationCokernel b R)))
    (equationEndomorphism a R).range.mkQ (LinearMap.exact_map_mkQ_range (equationEndomorphism a R))
    (equationEndomorphism a R).range.mkQ (LinearMap.exact_map_mkQ_range (equationEndomorphism a R))
    (Submodule.mkQ_surjective _) hb (equationEndomorphism b (equationCokernel a R))
      (equationEndomorphism_quotient b (equationEndomorphism a R).range).symm (Submodule.mkQ_surjective _)

theorem twoEquationBoundary_injective (ha : Function.Injective (equationEndomorphism a R)) :
    Function.Injective (twoEquationBoundary a b hb) := by
  apply (injective_iff_map_eq_zero (twoEquationBoundary a b hb)).mpr
  intro x hx
  obtain ⟨k, hk⟩ := (twoEquationBoundary_kernel_exact a b hb x).mp hx
  have hk0 : k = 0 := Subtype.ext (ha (k.2.trans (map_zero (equationEndomorphism a R)).symm))
  exact hk.symm.trans
    ((congrArg (equationKernelQuotient a (equationEndomorphism b R).range) hk0).trans (map_zero _))

/-- The two first-kernel correction modules are actually isomorphic. -/
def twoEquationKernelEquiv (ha : Function.Injective (equationEndomorphism a R)) :
    equationKernel a (equationCokernel b R) ≃ₗ[R] equationKernel b (equationCokernel a R) := by
  let u : equationKernel a (equationCokernel b R) →ₗ[R] equationKernel b (equationCokernel a R) :=
    LinearMap.codRestrict _ (twoEquationBoundary a b hb)
      (fun x => (twoEquationBoundary_range_exact a b hb).apply_apply_eq_zero x)
  refine LinearEquiv.ofBijective u ⟨?_, ?_⟩
  · intro x y h
    exact twoEquationBoundary_injective a b hb ha (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := (twoEquationBoundary_range_exact a b hb y.1).mp y.2
    exact ⟨x, Subtype.ext hx⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.MultiplicationSequence.BundleCycles
