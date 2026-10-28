import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleFieldTracePairing
import OAI.NumberTheory.PadicHodge.PeriodInvariants.TracePairingBasis
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteFreeFiberSurjectivity

/-! # Finite Etale Dual Basis -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleDualBasis

noncomputable section

/-! # Actual trace-dual bases for finite free étale algebras over arbitrary rings -/

open scoped TensorProduct

universe u v
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S] [Algebra.Etale R S]
  {ι : Type v} [Fintype ι] (b : Module.Basis ι R S)

theorem fiber_surjective (F : Type u) [Field F] [Algebra R F] :
    Function.Surjective ((TracePairingBasis.linear b).baseChange F) := by
  have : FiniteDimensional F (F ⊗[R] S) := inferInstance
  have hn : (Algebra.traceForm F (F ⊗[R] S)).Nondegenerate :=
    EtaleFieldTracePairing.Finite.nondegenerate F (F ⊗[R] S)
  have hs : Function.Surjective (TracePairingBasis.linear (b.baseChange F)) :=
    TracePairingBasis.surjective (b.baseChange F) hn
  have he : Function.Surjective ((TracePairingBasis.linear b).baseChange F) =
      Function.Surjective (TracePairingBasis.linear (b.baseChange F)) :=
    congrArg (fun f : (F ⊗[R] S) →ₗ[F] (F ⊗[R] S) => Function.Surjective f)
      (TracePairingBasis.baseChange b F)
  exact Eq.mpr he hs

theorem bijective : Function.Bijective (TracePairingBasis.linear b) := by
  apply FiniteFreeFiberSurjectivity.bijective
  intro m hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  exact fiber_surjective b (R ⧸ m)

def equiv : S ≃ₗ[R] S := LinearEquiv.ofBijective (TracePairingBasis.linear b) (bijective b)

def dualBasis : Module.Basis ι R S := b.map (equiv b).symm

theorem trace_basis_dual [DecidableEq ι] (i j : ι) :
    Algebra.trace R S (b i * dualBasis b j) = if i = j then 1 else 0 := by
  rw [← TracePairingBasis.coordinate b (dualBasis b j) i]
  have he : TracePairingBasis.linear b (dualBasis b j) = b j :=
    (equiv b).apply_symm_apply (b j)
  rw [he, b.equivFun_self]
  simp only [eq_comm]

theorem trace_dual_basis [DecidableEq ι] (i j : ι) :
    Algebra.trace R S (dualBasis b i * b j) = if i = j then 1 else 0 := by
  rw [mul_comm, trace_basis_dual]
  simp only [eq_comm]

theorem coordinate (i : ι) : Algebra.traceForm R S (dualBasis b i) = b.coord i := by
  classical
  apply b.ext
  intro j
  change Algebra.trace R S (dualBasis b i * b j) = b.repr (b j) i
  rw [trace_dual_basis, b.repr_self_apply]
  simp only [eq_comm]

theorem expansion (x : S) : (∑ i, Algebra.trace R S (dualBasis b i * x) • b i) = x := by
  have he : ∀ i, Algebra.trace R S (dualBasis b i * x) = b.repr x i :=
    fun i => LinearMap.congr_fun (coordinate b i) x
  simp only [he, b.sum_repr]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleDualBasis
