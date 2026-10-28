import OAI.RepresentationTheory.Theta.Geometric.Active.Basis
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalSpan

/-! # Cartan -/

namespace OAI.RepresentationTheory.Theta.Geometric.Active.Cartan.Spherical

noncomputable section

/-! ElementaryDivisors gives all active SL3 double cosets. Consequently the raw active
operators span the entire rational spherical algebra. -/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalSpan

variable (q : ℕ) [Fact q.Prime]

theorem exists_active_cartan (g : SphericalGU.Spherical.SL3 q) :
    ∃ a : Intrinsic.Hecke.ActiveWeight, DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q a) g := by
  obtain ⟨a, ⟨ha, hsum, U, V, he⟩, _⟩ :=
    Algebra.Modules.ElementaryDivisors.sl3_smith_normal_form (q : ℤ_[q]) PadicInt.irreducible_p g⁻¹
  let b : Intrinsic.Hecke.ActiveWeight := ⟨fun i => -a i,
    (fun _ _ hij => neg_le_neg (ha hij)), by simp only [Finset.sum_neg_distrib, hsum, neg_zero]⟩
  let F : Matrix.SpecialLinearGroup (Fin 3) ℤ_[q] →* SphericalGU.Spherical.SL3 q :=
    Matrix.SpecialLinearGroup.map (PadicInt.Coe.ringHom (p := q))
  have hdiag : Matrix.SpecialLinearGroup.toGL (Intrinsic.Hecke.activeSLRepresentative q b) =
      AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ b.val i) := Units.ext rfl
  have hd : ((Intrinsic.Hecke.activeSLRepresentative q b)⁻¹).val =
      Matrix.diagonal (fun i => (q : ℚ_[q]) ^ a i) := by
    have hi := congrArg (fun z : SphericalGU.Spherical.GL3 q => z.inv) hdiag
    change ((Intrinsic.Hecke.activeSLRepresentative q b)⁻¹).val =
      (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ b.val i)).inv at hi
    rw [hi]
    simp [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, b, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit]
  have hg : g⁻¹ = F U * (Intrinsic.Hecke.activeSLRepresentative q b)⁻¹ * F V := by
    apply Subtype.ext
    change (g⁻¹).val = (F U).val * ((Intrinsic.Hecke.activeSLRepresentative q b)⁻¹).val * (F V).val
    rw [hd]
    exact he
  refine ⟨b, ⟨⟨F V⁻¹, ⟨V⁻¹, rfl⟩⟩, ⟨F U⁻¹, ⟨U⁻¹, rfl⟩⟩, ?_⟩⟩
  simpa only [mul_inv_rev, inv_inv, map_inv, mul_assoc] using congrArg Inv.inv hg

theorem active_coset_covered (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) :
    ∃ a : Intrinsic.Hecke.ActiveWeight, c ∈ AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.doubleCosetOrbit (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q a) := by
  induction c using Quotient.inductionOn with
  | h g =>
    obtain ⟨a, l, r, hg⟩ := exists_active_cartan q g⁻¹
    refine ⟨a, (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.mem_doubleCosetOrbit _ _ _).mpr ⟨r⁻¹, l⁻¹, ?_⟩⟩
    simpa only [inv_inv, mul_inv_rev, Subgroup.coe_inv, mul_assoc] using congrArg Inv.inv hg

theorem active_raw_span (basis : Intrinsic.Hecke.ActiveWeight → SphericalGU.Spherical.SL3Hecke q)
    (hraw : ∀ a, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q a) (basis a)) :
    Submodule.span ℚ (Set.range basis) = ⊤ := by
  rw [← Finsupp.range_linearCombination]
  apply LinearMap.range_eq_top.mpr
  intro T
  obtain ⟨c, hc⟩ := AlgebraicGeometry.AbelianScheme.TateComparison.RationalSpan.exists_raw_rational_expansion (SphericalGU.Spherical.integralSL3 q)
    (Intrinsic.Hecke.activeSLRepresentative q) basis hraw (active_coset_covered q) T
  exact ⟨c, hc.symm⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Active.Cartan.Spherical
