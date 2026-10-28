import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke

/-! # Coset Shift -/

namespace OAI.RepresentationTheory.Theta.Geometric.CosetShift

noncomputable section

/-! Central clearing translates the original raw coset supports bijectively,
retaining the actual coset and the inverse-representative convention. -/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction

def rawCentralShiftEquiv {G : Type*} [Group G] (U : Subgroup G)
    (z : G) (hz : ∀ h : G, Commute h z) (g : G) :
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport U (z * g) ≃ AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport U g where
  toFun x := ⟨z • x.val, (AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.central_orbit_shift U z hz g x.val).mpr x.property⟩
  invFun x := ⟨z⁻¹ • x.val, (AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.central_orbit_shift U z hz g (z⁻¹ • x.val)).mp
    (by
      rw [smul_inv_smul]
      exact x.property)⟩
  left_inv x := Subtype.ext (inv_smul_smul z x.val)
  right_inv x := Subtype.ext (smul_inv_smul z x.val)

theorem rawCentralShiftEquiv_apply {G : Type*} [Group G] (U : Subgroup G)
    (z : G) (hz : ∀ h : G, Commute h z) (g : G)
    (x : AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport U (z * g)) :
    (rawCentralShiftEquiv U z hz g x).val = z • x.val := rfl

def rawLocalTypeShiftEquiv (s q : ℕ) [Fact q.Prime] (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType s) (n : ℕ) :
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q (t.shift n)) ≃
      AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q t) := by
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.representative_shift]
  exact rawCentralShiftEquiv _ (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.centralElement s q ^ n)
    (fun h => (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.centralElement_commutes s q h).pow_right n) _

def rawClearedActiveShiftEquiv (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s) (a : Intrinsic.Hecke.ActiveWeight) :
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q (Intrinsic.Hecke.clearedActiveType v a).val) ≃
      AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q (Intrinsic.Hecke.activeType v a)) :=
  rawLocalTypeShiftEquiv s q (Intrinsic.Hecke.activeType v a) (Intrinsic.Hecke.clearingExponent v a)

end

end OAI.RepresentationTheory.Theta.Geometric.CosetShift
