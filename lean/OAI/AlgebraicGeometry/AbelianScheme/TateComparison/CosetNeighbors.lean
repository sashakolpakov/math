import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConvolutionCoefficients
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity
import Mathlib.Data.Finsupp.Multiset

/-! # Coset Neighbors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CosetNeighbors

noncomputable section

/-! Exact multiset convolution on local cosets. Repeated endpoints are
retained, and chronological binding is reconciled with operator composition. -/

open scoped Classical

section Multisets

variable {X : Type*}

def multisetVector : Multiset X →+ (X →₀ ℚ) where
  toFun m := (m.map (fun x => Finsupp.single x (1 : ℚ))).sum
  map_zero' := by simp
  map_add' m n := by simp

@[simp]
theorem multisetVector_singleton (x : X) :
    multisetVector ({x} : Multiset X) = Finsupp.single x 1 := by
  change (Multiset.map _ {x}).sum = _
  rw [Multiset.map_singleton, Multiset.sum_singleton]

variable [DecidableEq X]

theorem multisetVector_apply (m : Multiset X) (x : X) :
    multisetVector m x = (m.count x : ℚ) := by
  induction m using Multiset.induction_on with
  | empty => simp [multisetVector]
  | @cons y m ih =>
    rw [← Multiset.singleton_add, map_add, Finsupp.add_apply, multisetVector_singleton, ih]
    by_cases h : y = x
    · subst y
      simp
      ring
    · simp [Ne.symm h]

theorem multisetVector_injective : Function.Injective (multisetVector (X := X)) := by
  intro m n h
  apply Multiset.ext.mpr
  intro x
  have hx := congrArg (fun f : X →₀ ℚ => f x) h
  rw [multisetVector_apply, multisetVector_apply] at hx
  exact_mod_cast hx

theorem exists_multisetVector (f : X →₀ ℚ) (hf : ∀ x, ∃ n : ℕ, f x = (n : ℚ)) :
    ∃ m : Multiset X, multisetVector m = f := by
  choose n hn using hf
  let c : X →₀ ℕ := Finsupp.onFinset f.support n (by
    intro x hx
    apply Finsupp.mem_support_iff.mpr
    rw [hn]
    exact_mod_cast hx)
  refine ⟨c.toMultiset, ?_⟩
  ext x
  rw [multisetVector_apply, Finsupp.count_toMultiset]
  exact (hn x).symm

omit [DecidableEq X] in
theorem multisetVector_bind (m : Multiset X) (N : X → Multiset X)
    (T : Module.End ℚ (X →₀ ℚ))
    (hN : ∀ x, multisetVector (N x) = T (Finsupp.single x 1)) :
    multisetVector (m.bind N) = T (multisetVector m) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons x m ih =>
    rw [Multiset.cons_bind, map_add, hN, ih, ← Multiset.singleton_add,
      map_add, map_add, multisetVector_singleton]

end Multisets

section Operators

variable {G : Type*} [Group G] (U : Subgroup G)

def cosetNeighbors (T : HeckeKernel.SphericalHecke U) (hT : HeckeKernel.NatValuedKernel U (HeckeKernel.kernel U T))
    (x : G ⧸ U) : Multiset (G ⧸ U) :=
  (exists_multisetVector (HeckeKernel.kernelColumn U (HeckeKernel.kernel U T) (HeckeKernel.kernel_invariant U T) x)
    (HeckeKernel.natValued_column U hT _ x)).choose

theorem cosetNeighbors_vector (T : HeckeKernel.SphericalHecke U) (hT : HeckeKernel.NatValuedKernel U (HeckeKernel.kernel U T))
    (x : G ⧸ U) :
    multisetVector (cosetNeighbors U T hT x) = T.val (Finsupp.single x 1) := by
  have h := (exists_multisetVector (HeckeKernel.kernelColumn U (HeckeKernel.kernel U T) (HeckeKernel.kernel_invariant U T) x)
    (HeckeKernel.natValued_column U hT _ x)).choose_spec
  change multisetVector (cosetNeighbors U T hT x) = _ at h
  rw [h]
  induction x using Quotient.inductionOn with
  | h x => exact (HeckeKernel.hecke_single U T x).symm

def heckeColumnLinear (x : G ⧸ U) : HeckeKernel.SphericalHecke U →ₗ[ℚ] HeckeKernel.CosetModule U where
  toFun T := T.val (Finsupp.single x 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cosetNeighbors_convolution {I : Type*} (basis : I → HeckeKernel.SphericalHecke U)
    (hnat : ∀ i, HeckeKernel.NatValuedKernel U (HeckeKernel.kernel U (basis i))) (u v : I) (c : I →₀ ℕ)
    (hconv : basis v * basis u = c.sum (fun w n => n • basis w)) (x : G ⧸ U) :
    (cosetNeighbors U (basis u) (hnat u) x).bind
        (cosetNeighbors U (basis v) (hnat v)) =
      c.sum (fun w n => n • cosetNeighbors U (basis w) (hnat w) x) := by
  apply multisetVector_injective
  rw [multisetVector_bind _ _ (basis v).val (cosetNeighbors_vector U (basis v) (hnat v)),
    cosetNeighbors_vector]
  have hc := congrArg (heckeColumnLinear U x) hconv
  change (basis v).val ((basis u).val (Finsupp.single x 1)) = _ at hc
  rw [hc]
  simp only [Finsupp.sum, map_sum, map_nsmul, cosetNeighbors_vector, heckeColumnLinear,
    LinearMap.coe_mk, AddHom.coe_mk]

end Operators

variable (s q : ℕ) [Fact q.Prime]

def sphericalCosetNeighbors (t : Local.LocalType s) :
    HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q → Multiset (HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q) :=
  cosetNeighbors _ (CentralConvolution.sphericalBasis s q t) (HeckeKernel.raw_natValued _ (CentralConvolution.sphericalBasis_isRaw s q t))

theorem sphericalCosetNeighbors_count (t : Local.LocalType s) (g : HeckeKernel.SplitGroup s q)
    (y : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q) :
    (sphericalCosetNeighbors s q t (QuotientGroup.mk g)).count y =
      if g⁻¹ • y ∈ HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t) then 1 else 0 := by
  have h := congrArg (fun f : HeckeKernel.CosetModule (HeckeKernel.integralLevel s q) => f y)
    (cosetNeighbors_vector (HeckeKernel.integralLevel s q) (CentralConvolution.sphericalBasis s q t)
      (HeckeKernel.raw_natValued _ (CentralConvolution.sphericalBasis_isRaw s q t)) (QuotientGroup.mk g))
  rw [multisetVector_apply, Gelfand.hecke_apply_single, one_mul,
    HeckeKernel.raw_kernel_at _ (CentralConvolution.sphericalBasis_isRaw s q t)] at h
  change ((sphericalCosetNeighbors s q t (QuotientGroup.mk g)).count y : ℚ) = _ at h
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- The same natural coefficients count chronological local chains,
including repeated terminal cosets. -/
theorem sphericalCosetNeighbors_convolution (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (u v : Local.IntegralType s) (x : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q) :
    (sphericalCosetNeighbors s q u.val x).bind (sphericalCosetNeighbors s q v.val) =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum
        (fun w n => n • sphericalCosetNeighbors s q w.val x) := by
  apply cosetNeighbors_convolution (HeckeKernel.integralLevel s q)
    (fun t : Local.IntegralType s => CentralConvolution.sphericalBasis s q t.val)
    (fun t => HeckeKernel.raw_natValued _ (CentralConvolution.sphericalBasis_isRaw s q t.val))
  rw [Commutativity.spherical_mul_comm s q hElementaryDivisors (CentralConvolution.sphericalBasis s q v.val), ConvolutionCoefficients.spherical_convolution]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CosetNeighbors
