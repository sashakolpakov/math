import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Padic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Span.Defs

/-! # Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Basis.Construction

noncomputable section

/-!
Elementary quotients in any q-adic lattice basis. The diagonal subgroup
is the actual span of q^(a_i) times the basis vectors; its quotient is
computed by the coordinate residue homomorphism.
-/

open _root_.Module
open scoped BigOperators

variable (q : ℕ) [Fact q.Prime] {d : ℕ}
  {V : Type*} [AddCommGroup V] [Module ℤ_[q] V]

def basisDiagonalSubmodule (b : Basis (Fin d) ℤ_[q] V) (a : Fin d → ℕ) : Submodule ℤ_[q] V :=
  Submodule.span ℤ_[q] (Set.range fun i => (q : ℤ_[q]) ^ a i • b i)

theorem mem_basisDiagonalSubmodule_iff
    (b : Basis (Fin d) ℤ_[q] V) (a : Fin d → ℕ) (x : V) :
    x ∈ basisDiagonalSubmodule q b a ↔
      ∀ i, b.repr x i ∈ Ideal.span {(q : ℤ_[q]) ^ a i} := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      by_cases hji : j = i
      · subst i
        simp only [map_smul, Finsupp.smul_apply, Basis.repr_self,
          Finsupp.single_eq_same, smul_eq_mul, mul_one]
        exact Ideal.mem_span_singleton.mpr (dvd_refl _)
      · simp [map_smul, Basis.repr_self, hji]
    | zero =>
      intro i
      simpa only [map_zero, Finsupp.coe_zero, Pi.zero_apply] using
        (Ideal.span {(q : ℤ_[q]) ^ a i}).zero_mem
    | add x y _ _ hx hy =>
      intro i
      simpa only [map_add, Finsupp.add_apply] using
        (Ideal.span {(q : ℤ_[q]) ^ a i}).add_mem (hx i) (hy i)
    | smul r x _ hx =>
      intro i
      simpa only [map_smul, Finsupp.smul_apply] using
        (Ideal.span {(q : ℤ_[q]) ^ a i}).smul_mem r (hx i)
  · intro hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hx i)
    rw [hc, mul_comm, mul_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self i))

def basisCoordinateResidues (b : Basis (Fin d) ℤ_[q] V) (a : Fin d → ℕ) :
    V →+ (∀ i, ZMod (q ^ a i)) :=
  (Padic.Construction.padicCoordinateResidues q a).comp b.equivFun.toAddEquiv.toAddMonoidHom

theorem basisCoordinateResidues_surjective (b : Basis (Fin d) ℤ_[q] V) (a : Fin d → ℕ) :
    Function.Surjective (basisCoordinateResidues q b a) :=
  (Padic.Construction.padicCoordinateResidues_surjective q a).comp b.equivFun.surjective

/-- The elementary-divisor span is exactly the kernel of the surjective
coordinate residue map, so it records the quotient group itself. -/
theorem basisCoordinateResidues_ker (b : Basis (Fin d) ℤ_[q] V) (a : Fin d → ℕ) :
    (basisCoordinateResidues q b a).ker = (basisDiagonalSubmodule q b a).toAddSubgroup := by
  ext x
  change (fun i => PadicInt.toZModPow (a i) (b.repr x i)) = 0 ↔
    x ∈ basisDiagonalSubmodule q b a
  rw [funext_iff, mem_basisDiagonalSubmodule_iff]
  apply forall_congr'
  intro i
  rw [← PadicInt.ker_toZModPow]
  rfl

def basisDiagonalQuotientEquiv (b : Basis (Fin d) ℤ_[q] V) (a : Fin d → ℕ) :
    V ⧸ (basisDiagonalSubmodule q b a).toAddSubgroup ≃+ (∀ i, ZMod (q ^ a i)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (basisCoordinateResidues_ker q b a).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (basisCoordinateResidues q b a)
      (basisCoordinateResidues_surjective q b a))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Basis.Construction
