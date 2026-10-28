import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalDifferentialNormalForm
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GaussianShortComplex
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexEndpointHomotopy

/-! # Local Outgoing Reduction -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalOutgoingReduction.Construction.LocalSectionLifting

noncomputable section

/-! Removing all invertible summands of the outgoing differential of a finite free complex. -/

open _root_.CategoryTheory

universe u

def shortComplexHomotopyEquivOfIso {C : Type*} [Category* C] [Preadditive C]
    {S T : ShortComplex C} (e : S ≅ T) : ShortComplex.HomotopyEquiv S T where
  hom := e.hom
  inv := e.inv
  homotopyHomInvId := ShortComplex.Homotopy.ofEq e.hom_inv_id
  homotopyInvHomId := ShortComplex.Homotopy.ofEq e.inv_hom_id

variable {R : Type u} [CommRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (P : LocalMinimalOf.Construction.LocalSectionLifting.LocalMinimalDifferential S.g.hom)

def localOutgoingPrecedingMap : S.X₁ →ₗ[R] (P.source × P.cancelled) :=
  P.sourceEquiv.symm.toLinearMap.comp S.f.hom

theorem localOutgoingPreceding_zero :
    (ComplexGaussian.Construction.LocalSectionLifting.blockDifferential P.differential 0 0 (LinearEquiv.refl R P.cancelled)).comp
      (localOutgoingPrecedingMap S P) = 0 := by
  apply LinearMap.ext
  intro x
  change (P.differential (P.sourceEquiv.symm (S.f x)).1 + 0,
    0 + (P.sourceEquiv.symm (S.f x)).2) = 0
  simp only [add_zero, zero_add]
  rw [← P.normal_form, LinearEquiv.apply_symm_apply, S.moduleCat_zero_apply, map_zero]

abbrev localOutgoingCoordinateComplex : ShortComplex (ModuleCat.{u} R) :=
  GaussianShortComplex.Construction.LocalSectionLifting.blockOutgoingComplex P.differential 0 0 (LinearEquiv.refl R P.cancelled)
    (localOutgoingPrecedingMap S P) (localOutgoingPreceding_zero S P)

abbrev localOutgoingReducedComplex : ShortComplex (ModuleCat.{u} R) :=
  GaussianShortComplex.Construction.LocalSectionLifting.schurOutgoingComplex P.differential 0 0 (LinearEquiv.refl R P.cancelled)
    (localOutgoingPrecedingMap S P) (localOutgoingPreceding_zero S P)

def localOutgoingCoordinateIso : S ≅ localOutgoingCoordinateComplex S P :=
  ShortComplex.isoMk (Iso.refl _) P.sourceEquiv.symm.toModuleIso P.targetEquiv.toModuleIso
    (by ext x; rfl)
    (by
      ext x
      change (P.differential (P.sourceEquiv.symm x).1 + 0,
        0 + (P.sourceEquiv.symm x).2) = P.targetEquiv (S.g x)
      simp only [add_zero, zero_add]
      rw [← P.normal_form, LinearEquiv.apply_symm_apply])

def localOutgoingReduction : ShortComplex.HomotopyEquiv S (localOutgoingReducedComplex S P) :=
  (shortComplexHomotopyEquivOfIso (localOutgoingCoordinateIso S P)).trans
    (GaussianShortComplex.Construction.LocalSectionLifting.blockOutgoingHomotopyEquiv P.differential 0 0 (LinearEquiv.refl R P.cancelled)
      (localOutgoingPrecedingMap S P) (localOutgoingPreceding_zero S P))

theorem localOutgoingReduction_hom_h₀ :
    (localOutgoingReduction S P).homotopyHomInvId.h₀ = 0 :=
  ShortComplexEndpointHomotopy.Construction.LocalSectionLifting.shortComplexHomotopyEquiv_trans_hom_h₀ _ _ rfl rfl

theorem localOutgoingReduction_inv_h₀ :
    (localOutgoingReduction S P).homotopyInvHomId.h₀ = 0 :=
  ShortComplexEndpointHomotopy.Construction.LocalSectionLifting.shortComplexHomotopyEquiv_trans_inv_h₀ _ _ rfl rfl

theorem localOutgoingReduced_residue_zero :
    (localOutgoingReducedComplex S P).g.hom.baseChange (IsLocalRing.ResidueField R) = 0 := by
  have hg : (localOutgoingReducedComplex S P).g.hom = P.differential := by
    apply LinearMap.ext
    intro x
    change P.differential x - 0 = P.differential x
    exact sub_zero _
  rw [hg]
  exact P.residue_zero

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalOutgoingReduction.Construction.LocalSectionLifting
