import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeterminantDivisibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.FreeQuotient
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Determinant

/-! # Split Lattice -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SplitLattice.SplitLatticeDeterminant

noncomputable section

/-! A prime-divisible Hodge submodule with projective quotient gives the required determinant valuation bound on an integral lattice. -/

variable (p : ℕ) [Fact p.Prime]
  {M I J : Type*} [AddCommGroup M] [Module ℤ_[p] M]
  [Fintype I] [Fintype J]

theorem of_split_basis (P Q : Submodule ℤ_[p] M) (hc : IsCompl P Q)
    (bP : Module.Basis I ℤ_[p] P) (bQ : Module.Basis J ℤ_[p] Q)
    (F : Module.End ℤ_[p] M) (hne : F.det ≠ 0)
    (hF : ∀ x : P, ∃ y : M, F x = (p : ℤ_[p]) • y) :
    (Fintype.card I : ℤ) ≤ Padic.valuation (F.det : ℚ_[p]) := by
  classical
  let b := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hc)
  let s : Finset (I ⊕ J) := Finset.univ.map Function.Embedding.inl
  let A := LinearMap.toMatrix b b F
  have hb (i : I) : b (Sum.inl i) = (bP i : M) := by
    simp only [b, Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl',
      Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd, Submodule.coe_zero, add_zero]
  have hd : ∀ j ∈ s, ∀ i, (p : ℤ_[p]) ∣ A i j := by
    intro j hj i
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨y, hy⟩ := hF (bP a)
    refine ⟨b.repr y i, ?_⟩
    change (LinearMap.toMatrix b b F) i (Sum.inl a) = (p : ℤ_[p]) * b.repr y i
    rw [LinearMap.toMatrix_apply, hb, hy, map_smul, Finsupp.smul_apply]
    rfl
  have hA : A.det ≠ 0 := by simpa only [A, LinearMap.det_toMatrix] using hne
  have hv := Integral.DeterminantDivisibility.IntegralDeterminantDivisibility.padic_valuation_ge p A s hA hd
  simpa only [s, Finset.card_map, Finset.card_univ, A, LinearMap.det_toMatrix] using hv

theorem valuation_ge {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]
    [Module.Free ℤ_[p] V] [Module.Finite ℤ_[p] V]
    (P : Submodule ℤ_[p] V) [Module.Projective ℤ_[p] (V ⧸ P)]
    (F : Module.End ℤ_[p] V) (hne : F.det ≠ 0)
    (hF : ∀ x : P, ∃ y : V, F x = (p : ℤ_[p]) • y) :
    (Module.finrank ℤ_[p] P : ℤ) ≤ Padic.valuation (F.det : ℚ_[p]) := by
  obtain ⟨Q, hQ⟩ := FreeQuotient.FreeQuotientComplement.exists_complement P
  let : Fintype (Module.Free.ChooseBasisIndex ℤ_[p] P) := Fintype.ofFinite _
  let : Fintype (Module.Free.ChooseBasisIndex ℤ_[p] Q) := Fintype.ofFinite _
  have hv := of_split_basis p P Q hQ (Module.Free.chooseBasis ℤ_[p] P)
    (Module.Free.chooseBasis ℤ_[p] Q) F hne hF
  simpa only [← Module.finrank_eq_card_chooseBasisIndex] using hv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SplitLattice.SplitLatticeDeterminant
