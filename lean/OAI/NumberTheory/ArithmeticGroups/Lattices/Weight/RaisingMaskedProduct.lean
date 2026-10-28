import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingCoordinateMask
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingProductCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.NilSubmoduleAffineHomeomorphism

/-! # Raising Masked Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingMaskedProduct.Construction

noncomputable section

/-! Complementary entry masks give global product coordinates on
the ambient positive unipotent group. -/

open NormedSpace

theorem weightRaising_masked_exponential_product
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (r : Fin m → Fin m → Prop) :
    ∃ e : (RaisingCoordinateMask.Construction.weightRaisingCoordinateMask b w r).range × (RaisingCoordinateMask.Construction.weightRaisingCoordinateMask b w r).ker ≃ₜ
      Positive.DerivationNilpotence.Construction.weightRaisingOperators b w,
      ∀ p, (e p).val = exp p.1.val.val * exp p.2.val.val - 1 := by
  let P := RaisingCoordinateMask.Construction.weightRaisingCoordinateMask b w r
  apply RaisingProductCoordinates.Construction.weightRaising_exists_exponential_product_homeomorph b H hH w heig P.range P.ker
    (LinearMap.IsIdempotentElem.isCompl (RaisingCoordinateMask.Construction.weightRaisingCoordinateMask_idempotent b w r))
  · intro t X hX
    obtain ⟨Y, rfl⟩ := hX
    exact ⟨RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t Y,
      RaisingCoordinateMask.Construction.weightRaisingCoordinateMask_flow_commute b H hH w heig r t Y⟩
  · intro t X hX
    change P X = 0 at hX
    change P (RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t X) = 0
    rw [RaisingCoordinateMask.Construction.weightRaisingCoordinateMask_flow_commute b H hH w heig r t X, hX, map_zero]

theorem weightRaising_mask_range_support
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (r : Fin m → Fin m → Prop) (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)
    (hX : X ∈ (RaisingCoordinateMask.Construction.weightRaisingCoordinateMask b w r).range) (i j : Fin m) (hij : ¬r i j) :
    b.repr (X.val (b j)) i = 0 := by
  obtain ⟨Y, rfl⟩ := hX
  rw [RaisingCoordinateMask.Construction.weightRaisingCoordinateMask_entry, ite_eq_right hij]

theorem weightRaising_mask_kernel_support
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (r : Fin m → Fin m → Prop) (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)
    (hX : X ∈ (RaisingCoordinateMask.Construction.weightRaisingCoordinateMask b w r).ker) (i j : Fin m) (hij : r i j) :
    b.repr (X.val (b j)) i = 0 := by
  have he := congrArg (fun Y : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w => b.repr (Y.val (b j)) i) hX
  simpa only [RaisingCoordinateMask.Construction.weightRaisingCoordinateMask_entry, ite_eq_left hij, ZeroMemClass.coe_zero,
    zero_apply, map_zero, PiLp.zero_apply] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingMaskedProduct.Construction
