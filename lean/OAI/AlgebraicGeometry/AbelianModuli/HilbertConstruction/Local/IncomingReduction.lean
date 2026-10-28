import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.OutgoingReduction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianIncomingComplex

/-! # Incoming Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.IncomingReduction.LocalSectionLifting

noncomputable section

/-! Removing the invertible summands of an incoming differential while preserving residue vanishing. -/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (P : MinimalDifferential.LocalSectionLifting.LocalMinimalDifferential S.f.hom)

def localIncomingFollowingMap : (P.target × P.cancelled) →ₗ[R] S.X₃ :=
  S.g.hom.comp P.targetEquiv.symm.toLinearMap

theorem localIncomingFollowing_zero :
    (localIncomingFollowingMap S P).comp
      (ComplexGaussian.LocalSectionLifting.blockDifferential P.differential 0 0 (LinearEquiv.refl R P.cancelled)) = 0 := by
  apply LinearMap.ext
  intro x
  change S.g (P.targetEquiv.symm (P.differential x.1 + 0, 0 + x.2)) = 0
  simp only [add_zero, zero_add]
  rw [← P.normal_form, LinearEquiv.symm_apply_apply, S.moduleCat_zero_apply]

abbrev localIncomingCoordinateComplex : ShortComplex (ModuleCat.{u} R) :=
  GaussianIncomingComplex.LocalSectionLifting.blockIncomingComplex P.differential 0 0 (LinearEquiv.refl R P.cancelled)
    (localIncomingFollowingMap S P) (localIncomingFollowing_zero S P)

abbrev localIncomingReducedComplex : ShortComplex (ModuleCat.{u} R) :=
  GaussianIncomingComplex.LocalSectionLifting.schurIncomingComplex P.differential 0 0 (LinearEquiv.refl R P.cancelled)
    (localIncomingFollowingMap S P) (localIncomingFollowing_zero S P)

def localIncomingCoordinateIso : S ≅ localIncomingCoordinateComplex S P :=
  ShortComplex.isoMk P.sourceEquiv.symm.toModuleIso P.targetEquiv.toModuleIso (Iso.refl _)
    (by
      ext x
      change (P.differential (P.sourceEquiv.symm x).1 + 0,
        0 + (P.sourceEquiv.symm x).2) = P.targetEquiv (S.f x)
      simp only [add_zero, zero_add]
      rw [← P.normal_form, LinearEquiv.apply_symm_apply])
    (by
      ext x
      change S.g (P.targetEquiv.symm (P.targetEquiv x)) = S.g x
      rw [LinearEquiv.symm_apply_apply])

def localIncomingReduction : ShortComplex.HomotopyEquiv S (localIncomingReducedComplex S P) :=
  (OutgoingReduction.LocalSectionLifting.shortComplexHomotopyEquivOfIso (localIncomingCoordinateIso S P)).trans
    (GaussianIncomingComplex.LocalSectionLifting.blockIncomingHomotopyEquiv P.differential 0 0 (LinearEquiv.refl R P.cancelled)
      (localIncomingFollowingMap S P) (localIncomingFollowing_zero S P))

theorem localIncomingReduction_hom_h₀ :
    (localIncomingReduction S P).homotopyHomInvId.h₀ = 0 :=
  ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquiv_trans_hom_h₀ _ _ rfl rfl

theorem localIncomingReduction_inv_h₀ :
    (localIncomingReduction S P).homotopyInvHomId.h₀ = 0 :=
  ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquiv_trans_inv_h₀ _ _ rfl rfl

theorem localIncomingReduced_residue_zero :
    (localIncomingReducedComplex S P).f.hom.baseChange (IsLocalRing.ResidueField R) = 0 := by
  have hf : (localIncomingReducedComplex S P).f.hom = P.differential := by
    apply LinearMap.ext
    intro x
    change P.differential x - 0 = P.differential x
    exact sub_zero _
  rw [hf]
  exact P.residue_zero

theorem localIncomingReduced_preserves_outgoing_residue_zero
    (hg : S.g.hom.baseChange (IsLocalRing.ResidueField R) = 0) :
    (localIncomingReducedComplex S P).g.hom.baseChange (IsLocalRing.ResidueField R) = 0 := by
  change ((S.g.hom.comp P.targetEquiv.symm.toLinearMap).comp
    (LinearMap.inl R P.target P.cancelled)).baseChange (IsLocalRing.ResidueField R) = 0
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, hg,
    LinearMap.zero_comp, LinearMap.zero_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.IncomingReduction.LocalSectionLifting
