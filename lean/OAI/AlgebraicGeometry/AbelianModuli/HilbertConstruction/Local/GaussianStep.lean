import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.Matrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSplitCoordinate
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.MapBlocks

/-! # Gaussian Step -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.GaussianStep.LocalSectionLifting

noncomputable section

/-! A nonzero residue differential has an invertible summand that can be cancelled. -/

variable {R M N ι κ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Fintype ι] [Fintype κ]
    (bM : Module.Basis ι R M) (bN : Module.Basis κ R N) (f : M →ₗ[R] N) (i : ι) (j : κ)

def basisBlockDifferential : (({l : ι // l ≠ i} → R) × R) →ₗ[R]
    (({l : κ // l ≠ j} → R) × R) :=
  (BasisSplitCoordinate.LocalSectionLifting.basisSplitCoordinate bN j).toLinearMap.comp
    (f.comp (BasisSplitCoordinate.LocalSectionLifting.basisSplitCoordinate bM i).symm.toLinearMap)

theorem basisBlockDifferential_scalar (r : R) :
    (basisBlockDifferential bM bN f i j (0, r)).2 = r * bN.repr (f (bM i)) j := by
  change (BasisSplitCoordinate.LocalSectionLifting.basisSplitCoordinate bN j (f ((BasisSplitCoordinate.LocalSectionLifting.basisSplitCoordinate bM i).symm (0, r)))).2 = _
  rw [BasisSplitCoordinate.LocalSectionLifting.basisSplitCoordinate_symm_scalar, BasisSplitCoordinate.LocalSectionLifting.basisSplitCoordinate_scalar, map_smul, map_smul]
  rfl

theorem basisBlockDifferential_eq_blocks (h : IsUnit (bN.repr (f (bM i)) j)) :
    basisBlockDifferential bM bN f i j =
      ComplexGaussian.LocalSectionLifting.blockDifferential (Linear.MapBlocks.LocalSectionLifting.linearMapBlock00 (basisBlockDifferential bM bN f i j))
        (Linear.MapBlocks.LocalSectionLifting.linearMapBlock01 (basisBlockDifferential bM bN f i j))
        (Linear.MapBlocks.LocalSectionLifting.linearMapBlock10 (basisBlockDifferential bM bN f i j))
        (LinearEquiv.smulOfUnit h.unit : R ≃ₗ[R] R) := by
  apply Linear.MapBlocks.LocalSectionLifting.linearMap_eq_blocks
  intro r
  rw [basisBlockDifferential_scalar]
  change r * bN.repr (f (bM i)) j = (h.unit : R) * r
  rw [h.unit_spec, mul_comm]

theorem exists_gaussian_step_of_unit_coefficient (h : IsUnit (bN.repr (f (bM i)) j)) :
    ∃ (eM : (({l : ι // l ≠ i} → R) × R) ≃ₗ[R] M)
      (eN : N ≃ₗ[R] (({l : κ // l ≠ j} → R) × R))
      (f' : ({l : ι // l ≠ i} → R) →ₗ[R] ({l : κ // l ≠ j} → R))
      (d : R ≃ₗ[R] R),
      ∀ x, eN (f (eM x)) = (f' x.1, d x.2) := by
  let F := basisBlockDifferential bM bN f i j
  let a := Linear.MapBlocks.LocalSectionLifting.linearMapBlock00 F
  let b := Linear.MapBlocks.LocalSectionLifting.linearMapBlock01 F
  let c := Linear.MapBlocks.LocalSectionLifting.linearMapBlock10 F
  let d : R ≃ₗ[R] R := LinearEquiv.smulOfUnit h.unit
  let eM := (ComplexGaussian.LocalSectionLifting.blockSourceShear c d).trans (BasisSplitCoordinate.LocalSectionLifting.basisSplitCoordinate bM i).symm
  let eN := (BasisSplitCoordinate.LocalSectionLifting.basisSplitCoordinate bN j).trans (ComplexGaussian.LocalSectionLifting.blockTargetShear b d)
  refine ⟨eM, eN, ComplexGaussian.LocalSectionLifting.schurDifferential a b c d, d, ?_⟩
  intro x
  change ComplexGaussian.LocalSectionLifting.blockTargetShear b d (F (ComplexGaussian.LocalSectionLifting.blockSourceShear c d x)) = _
  have hF : F = ComplexGaussian.LocalSectionLifting.blockDifferential a b c d := basisBlockDifferential_eq_blocks bM bN f i j h
  rw [hF]
  exact ComplexGaussian.LocalSectionLifting.blockDifferential_normal_form a b c d x

include bM bN in
theorem exists_gaussian_step_of_residue_ne_zero [IsLocalRing R]
    (hf : f.baseChange (IsLocalRing.ResidueField R) ≠ 0) :
    ∃ (i : ι) (j : κ)
      (eM : (({l : ι // l ≠ i} → R) × R) ≃ₗ[R] M)
      (eN : N ≃ₗ[R] (({l : κ // l ≠ j} → R) × R))
      (f' : ({l : ι // l ≠ i} → R) →ₗ[R] ({l : κ // l ≠ j} → R))
      (d : R ≃ₗ[R] R),
      ∀ x, eN (f (eM x)) = (f' x.1, d x.2) := by
  obtain ⟨i, j, hij⟩ := Residue.Matrix.LocalSectionLifting.exists_unit_matrix_coefficient_of_residue_ne_zero bM bN f hf
  exact ⟨i, j, exists_gaussian_step_of_unit_coefficient bM bN f i j hij⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.GaussianStep.LocalSectionLifting
