import OAI.RepresentationTheory.Theta.Geometric.Cleared.LocalInverseLattice
import OAI.RepresentationTheory.Theta.Geometric.Cleared.LocalMatrices

/-! # Local Relative Position -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The centrally cleared original matrices have precisely the local
relative positions prescribed by TateComparison, with inverse lattice conventions. -/

set_option backward.isDefEq.respectTransparency false

theorem Cleared.LocalRelativePosition.scalar_blockDiagonal (q : ℕ) [Fact q.Prime] (n : ℕ) (a : Fin 3 → ℤ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) * AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q a =
      AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => a i + (n : ℤ)) := by
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) =
      AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.diagonalHom (fun _ : Fin 3 => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) := Units.ext rfl
  rw [hs]
  change AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.diagonalHom _ * AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.diagonalHom _ = AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.diagonalHom _
  rw [← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, zpow_add, zpow_natCast, mul_comm]

theorem Cleared.LocalRelativePosition.scalar_blockDiagonal_zero (q : ℕ) [Fact q.Prime] (n : ℕ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) =
      AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun _ : Fin 3 => (n : ℤ)) := by
  apply Units.ext
  rfl

theorem Cleared.LocalRelativePosition.scaled_special_doubleCoset (q : ℕ) [Fact q.Prime]
    (n : ℕ) (a g : SphericalGU.Spherical.SL3 q)
    (h : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q) a g) :
    DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralGL3 q)
      (Matrix.GeneralLinearGroup.scalar (Fin 3) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) * Matrix.SpecialLinearGroup.toGL a)
      (Matrix.GeneralLinearGroup.scalar (Fin 3) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) * Matrix.SpecialLinearGroup.toGL g) := by
  obtain ⟨u, v, rfl⟩ := h
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL u.val, (Lattices.Spherical.toGL_integral_iff q _).mpr u.property⟩,
    ⟨Matrix.SpecialLinearGroup.toGL v.val, (Lattices.Spherical.toGL_integral_iff q _).mpr v.property⟩, ?_⟩
  simp only [map_mul]
  rw [← mul_assoc, ← mul_assoc, Matrix.GeneralLinearGroup.scalar_commute]
  simp only [mul_assoc]

theorem Cleared.LocalRelativePosition.inverse_matrix_relativePosition (q : ℕ) [Fact q.Prime]
    (a : Fin 3 → ℤ) (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q])
    (h : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralGL3 q) (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q a) g) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) a (AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionChoices.standardRankThreeLattice q) (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets.Construction.matrixBlockLattice q g⁻¹) := by
  obtain ⟨u, v, he⟩ := Cleared.LocalMatrices.inDoubleCoset_inv (SphericalGU.Spherical.integralGL3 q) h
  obtain ⟨U, hU⟩ := u.property
  obtain ⟨V, hV⟩ := v.property
  have hf : ∃ U V : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q],
      g⁻¹ = Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) U *
        AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => -a i) * Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) V :=
    ⟨U, V, by simpa only [hU, hV, AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal_inv] using he⟩
  exact (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.block_smith_iff_factorization q g⁻¹ (fun i => -a i)).mpr hf

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.clearedLocalMatrix_chosen_doubleCoset (hc : D.HasFiniteCoordinates)
    (a : Intrinsic.Hecke.ActiveWeight) (g : D.RationalSU) (haway : D.away g ∈ D.awayLevel)
    (hcos : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
      (Intrinsic.Hecke.activeSLRepresentative q a)⁻¹ (D.activeLocal g)⁻¹) (v : Fin s) :
    DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralGL3 q)
      (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q ((Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a).val.exponent v))
      (Data.ActiveHeckeThetaData.clearedLocalMatrix g (Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a) (v, false)) := by
  let n := Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a
  by_cases hv : v = D.pel.reference.distinguished
  · subst v
    have hi : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
        (Intrinsic.Hecke.activeSLRepresentative q a) (D.activeLocal g) := by
      simpa only [inv_inv] using Cleared.LocalMatrices.inDoubleCoset_inv (SphericalGU.Spherical.integralSL3 q) hcos
    have H := Cleared.LocalRelativePosition.scaled_special_doubleCoset q n _ _ hi
    have he : Matrix.SpecialLinearGroup.toGL (Intrinsic.Hecke.activeSLRepresentative q a) = AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q a.val :=
      Units.ext rfl
    rw [he, Cleared.LocalRelativePosition.scalar_blockDiagonal] at H
    have hexp : (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a).val.exponent D.pel.reference.distinguished =
        fun i => a.val i + (n : ℤ) := by
      funext i
      change (if D.pel.reference.distinguished = D.pel.reference.distinguished then a.val i else 0) +
        (n : ℤ) = _
      rw [ite_eq_left rfl]
    rw [hexp]
    exact H
  · have hg : D.localMatrix (v, false) g ∈ SphericalGU.Spherical.integralSL3 q :=
      ((hc.2.2 g).mp haway).2 (v, false) hv
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL (D.localMatrix (v, false) g),
      (Lattices.Spherical.toGL_integral_iff q _).mpr hg⟩, 1, ?_⟩
    have he : (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a).val.exponent v =
        fun _ => (n : ℤ) := by
      funext i
      simp only [Intrinsic.Hecke.clearedActiveType, AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.shift, Intrinsic.Hecke.activeType, ite_eq_right hv, zero_add]
      rfl
    rw [he, ← Cleared.LocalRelativePosition.scalar_blockDiagonal_zero]
    change Matrix.GeneralLinearGroup.scalar (Fin 3) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) * _ =
      _ * Matrix.GeneralLinearGroup.scalar (Fin 3) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) * 1
    rw [mul_one, Matrix.GeneralLinearGroup.scalar_commute]

theorem Data.ActiveHeckeThetaData.clearedLocalInverseLattice_relativePosition (hc : D.HasFiniteCoordinates)
    (a : Intrinsic.Hecke.ActiveWeight) (g : D.RationalSU) (haway : D.away g ∈ D.awayLevel)
    (hcos : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
      (Intrinsic.Hecke.activeSLRepresentative q a)⁻¹ (D.activeLocal g)⁻¹) (v : Fin s) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) ((Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a).val.exponent v)
      (AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionChoices.standardRankThreeLattice q)
      (Data.ActiveHeckeThetaData.clearedLocalInverseLattice g (Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a) (v, false)) :=
  Cleared.LocalRelativePosition.inverse_matrix_relativePosition q _ _ (D.clearedLocalMatrix_chosen_doubleCoset hc a g haway hcos v)

end

end OAI.RepresentationTheory.Theta.Geometric
