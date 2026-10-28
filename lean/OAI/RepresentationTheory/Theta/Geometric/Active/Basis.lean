import OAI.RepresentationTheory.Theta.Geometric.Active.Algebra
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action

/-! # Basis -/

namespace OAI.RepresentationTheory.Theta.Geometric.Active.Basis.Spherical

noncomputable section

/-! The active algebra equivalence preserves the unscaled characteristic
double-coset normalization of the supplied TateComparison basis. -/

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

theorem active_doubleCoset_iff (g h : SphericalGU.Spherical.SL3 q) :
    DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g) (SphericalGU.Spherical.activeEmbedding q v h) ↔
      DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q) g h := by
  constructor
  · rintro ⟨a, b, hab⟩
    apply (DoubleCosets.Spherical.special_doubleCoset_iff q g h).mp
    refine ⟨⟨a.val.1 v, ((Cosets.Spherical.mem_integralSplitGU_iff q a.val).mp a.property).1 v⟩,
      ⟨b.val.1 v, ((Cosets.Spherical.mem_integralSplitGU_iff q b.val).mp b.property).1 v⟩, ?_⟩
    have hmatrix := congrArg (fun z : SphericalGU.Spherical.SplitGU q s => z.1 v) hab
    change (SphericalGU.Spherical.activeEmbedding q v h).1 v =
      a.val.1 v * (SphericalGU.Spherical.activeEmbedding q v g).1 v * b.val.1 v at hmatrix
    simpa only [Cosets.Spherical.activeEmbedding_self] using hmatrix
  · rintro ⟨a, b, hab⟩
    refine ⟨⟨SphericalGU.Spherical.activeEmbedding q v a.val, (Cosets.Spherical.activeEmbedding_integral_iff q v a.val).mpr a.property⟩,
      ⟨SphericalGU.Spherical.activeEmbedding q v b.val, (Cosets.Spherical.activeEmbedding_integral_iff q v b.val).mpr b.property⟩, ?_⟩
    simpa only [map_mul] using congrArg (SphericalGU.Spherical.activeEmbedding q v) hab

theorem activeRestriction_raw (g : SphericalGU.Spherical.SL3 q) (T : SphericalGU.Spherical.activeAlgebra q v)
    (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g) T.val) :
    AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) g (Cosets.Spherical.activeRestrictionHom q v T) := by
  classical
  intro h
  have he := congrArg (fun w : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSplitGU q s) =>
    w (Cosets.Spherical.activeCosetMap q v (QuotientGroup.mk h))) (Cosets.Spherical.activeRestriction_kernel q v T)
  rw [IntegralKernel.Spherical.activeModuleMap_apply] at he
  rw [he]
  have hraw := hT (SphericalGU.Spherical.activeEmbedding q v h)
  change SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) T.val (QuotientGroup.mk (SphericalGU.Spherical.activeEmbedding q v h)) = _
  rw [hraw]
  have hd := active_doubleCoset_iff q v g⁻¹ h
  rw [map_inv] at hd
  change (if DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g)⁻¹
    (SphericalGU.Spherical.activeEmbedding q v h) then 1 else 0) =
    if DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q) g⁻¹ h then 1 else 0
  rw [hd]

theorem representative_activeType (a : Intrinsic.Hecke.ActiveWeight) :
    AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q (Intrinsic.Hecke.activeType v a) = SphericalGU.Spherical.activeEmbedding q v (Intrinsic.Hecke.activeSLRepresentative q a) := by
  apply Prod.ext
  · funext w
    by_cases hw : w = v
    · subst w
      apply Units.ext
      simp [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative, Intrinsic.Hecke.activeType, SphericalGU.Spherical.activeEmbedding, Intrinsic.Hecke.activeSLRepresentative,
        Matrix.SpecialLinearGroup.toGL]
    · apply Units.ext
      simp [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative, Intrinsic.Hecke.activeType, SphericalGU.Spherical.activeEmbedding, hw, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit]
  · simp [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative, Intrinsic.Hecke.activeType, SphericalGU.Spherical.activeEmbedding]

theorem active_basis_matching (basis : AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType s → SphericalGU.Spherical.FullHecke q s)
    (hbasis : ∀ t, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSplitGU q s) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t))
    (a : Intrinsic.Hecke.ActiveWeight) :
    ∃ T : SphericalGU.Spherical.SL3Hecke q,
      AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q a) T ∧
      Intrinsic.Action.activeHeckeMap q v (Algebra.Spherical.activeHeckeEquiv q v) T = basis (Intrinsic.Hecke.activeType v a) := by
  have hraw := hbasis (Intrinsic.Hecke.activeType v a)
  rw [representative_activeType q v a] at hraw
  have hmem := Algebra.Spherical.raw_active_mem_active q v (SphericalGU.Spherical.activeEmbedding q v (Intrinsic.Hecke.activeSLRepresentative q a))
    ((show (SphericalGU.Spherical.activeEmbedding q v).range ≤ SphericalGU.Spherical.activeSector q v from le_sup_right) ⟨_, rfl⟩)
    (basis (Intrinsic.Hecke.activeType v a)) hraw
  let T : SphericalGU.Spherical.activeAlgebra q v := ⟨basis (Intrinsic.Hecke.activeType v a), hmem⟩
  refine ⟨Cosets.Spherical.activeRestrictionHom q v T, activeRestriction_raw q v _ T hraw, ?_⟩
  change (Algebra.Spherical.activeHeckeEquiv q v (Cosets.Spherical.activeRestrictionHom q v T)).val = _
  rw [Algebra.Spherical.activeHeckeEquiv_restriction]

end

end OAI.RepresentationTheory.Theta.Geometric.Active.Basis.Spherical
