import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Finite Free Completion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFreeCompletion.Lifts

noncomputable section

/-!
Finite free modules over an adically complete ring are complete.
The limit is constructed coordinate by coordinate in an actual finite
basis. This supplies completeness of the finite evaluation integer ring.
-/

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R)

theorem basis_mem_ideal_smul_top_iff (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      simpa only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] using
        I.mul_mem_right (b.repr y i) hr
    · intro y z hy hz
      simpa only [map_add, Finsupp.coe_add, Pi.add_apply] using I.add_mem hy hz
  · intro hx
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top)

theorem basis_smodEq_iff (x y : M) :
    x ≡ y [SMOD I • (⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD I • (⊤ : Submodule R R)] := by
  simp only [SModEq.sub_mem, basis_mem_ideal_smul_top_iff b I, map_sub,
    Finsupp.coe_sub, Pi.sub_apply, Ideal.smul_eq_mul, Ideal.mul_top]

include b in
theorem finite_basis_adic_complete [IsAdicComplete I R] : IsAdicComplete I M := by
  classical
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.repr.injective
    ext i
    have hi : ∀ n, b.repr x i ≡ 0 [SMOD I ^ n • (⊤ : Submodule R R)] := by
      intro n
      simpa only [map_zero, Finsupp.coe_zero, Pi.zero_apply] using
        (basis_smodEq_iff b (I ^ n) x 0).mp (hx n) i
    simpa only [map_zero, Finsupp.coe_zero, Pi.zero_apply] using IsHausdorff.haus' (I := I) _ hi
  · intro f hf
    have hc (i : ι) : ∃ z : R, ∀ n, b.repr (f n) i ≡ z
        [SMOD I ^ n • (⊤ : Submodule R R)] := by
      apply IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i)
      intro m n hmn
      exact (basis_smodEq_iff b (I ^ m) (f m) (f n)).mp (hf hmn) i
    choose z hz using hc
    let l : M := b.equivFun.symm z
    have hl (i : ι) : b.repr l i = z i :=
      congrFun (b.equivFun.apply_symm_apply z) i
    refine ⟨l, fun n => (basis_smodEq_iff b (I ^ n) (f n) l).mpr ?_⟩
    intro i
    rw [hl]
    exact hz i n

variable (R M)

/-- No basis or limits are supplied to this construction: choose a finite
free basis and construct its coordinate limits using completeness of R. -/
theorem finite_free_adic_complete [Module.Free R M] [Module.Finite R M]
    [IsAdicComplete I R] : IsAdicComplete I M := by
  classical
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex R M)
  exact finite_basis_adic_complete (Module.Free.chooseBasis R M) I

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFreeCompletion.Lifts
