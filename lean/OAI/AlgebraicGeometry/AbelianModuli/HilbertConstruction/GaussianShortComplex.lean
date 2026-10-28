import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianContraction
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Preadditive

/-! # Gaussian Short Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianShortComplex.LocalSectionLifting

noncomputable section

/-! Gaussian cancellation for the outgoing differential of a short complex. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
    {E A B C D : Type v}
    [AddCommGroup E] [Module R E] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup D] [Module R D]
    (a : A →ₗ[R] C) (b : B →ₗ[R] C) (c : A →ₗ[R] D) (d : B ≃ₗ[R] D)
    (e : E →ₗ[R] (A × B)) (he : (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d).comp e = 0)

abbrev blockOutgoingComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk e (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d) he

include he in
theorem schurOutgoing_zero :
    (ComplexGaussian.LocalSectionLifting.schurDifferential a b c d).comp ((LinearMap.fst R A B).comp e) = 0 := by
  apply LinearMap.ext
  intro x
  change ComplexGaussian.LocalSectionLifting.schurDifferential a b c d (e x).1 = 0
  rw [← GaussianContraction.LocalSectionLifting.block_projection_differential a b c d]
  have hx : ComplexGaussian.LocalSectionLifting.blockDifferential a b c d (e x) = 0 := LinearMap.congr_fun he x
  rw [hx, map_zero]

abbrev schurOutgoingComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk ((LinearMap.fst R A B).comp e) (ComplexGaussian.LocalSectionLifting.schurDifferential a b c d)
    (schurOutgoing_zero a b c d e he)

def blockOutgoingProjection : blockOutgoingComplex a b c d e he ⟶
    schurOutgoingComplex a b c d e he where
  τ₁ := 𝟙 _
  τ₂ := ModuleCat.ofHom (LinearMap.fst R A B)
  τ₃ := ModuleCat.ofHom (GaussianCokernel.LocalSectionLifting.blockCokernelProjection b d)
  comm₁₂ := rfl
  comm₂₃ := by
    ext x
    exact (GaussianContraction.LocalSectionLifting.block_projection_differential a b c d x).symm

def blockOutgoingInclusion : schurOutgoingComplex a b c d e he ⟶
    blockOutgoingComplex a b c d e he where
  τ₁ := 𝟙 _
  τ₂ := ModuleCat.ofHom (GaussianContraction.LocalSectionLifting.blockSourceInclusion c d)
  τ₃ := ModuleCat.ofHom (LinearMap.inl R C D)
  comm₁₂ := by
    ext x
    exact (GaussianContraction.LocalSectionLifting.block_source_retraction_on_kernel a b c d (e x) (LinearMap.congr_fun he x)).symm
  comm₂₃ := by
    ext x
    exact GaussianContraction.LocalSectionLifting.block_differential_inclusion a b c d x

theorem blockOutgoing_inclusion_projection :
    blockOutgoingInclusion a b c d e he ≫ blockOutgoingProjection a b c d e he =
      𝟙 (schurOutgoingComplex a b c d e he) := by
  apply ShortComplex.Hom.ext
  · rfl
  · ext x
    exact GaussianContraction.LocalSectionLifting.block_source_retraction c d x
  · ext x
    exact GaussianContraction.LocalSectionLifting.block_target_retraction b d x

def blockOutgoing_contraction : ShortComplex.Homotopy
    (blockOutgoingProjection a b c d e he ≫ blockOutgoingInclusion a b c d e he)
    (𝟙 (blockOutgoingComplex a b c d e he)) where
  h₀ := 0
  h₁ := 0
  h₂ := ModuleCat.ofHom (-GaussianContraction.LocalSectionLifting.blockContractingMap d)
  h₃ := 0
  h₀_f := by
    ext x
    exact map_zero e
  g_h₃ := by ext x; rfl
  comm₁ := by
    ext x
    change E at x
    change x = (0 : E) + 0 + x
    simp
  comm₂ := by
    ext x
    change A × B at x
    change GaussianContraction.LocalSectionLifting.blockSourceInclusion c d x.1 =
      -GaussianContraction.LocalSectionLifting.blockContractingMap d (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d x) + e 0 + x
    rw [GaussianContraction.LocalSectionLifting.block_source_contraction a b c d x, map_zero]
    abel
  comm₃ := by
    ext x
    change C × D at x
    change (GaussianCokernel.LocalSectionLifting.blockCokernelProjection b d x, (0 : D)) =
      0 + ComplexGaussian.LocalSectionLifting.blockDifferential a b c d (-GaussianContraction.LocalSectionLifting.blockContractingMap d x) + x
    rw [GaussianContraction.LocalSectionLifting.block_target_contraction a b c d x, map_neg]
    abel

def blockOutgoingHomotopyEquiv : ShortComplex.HomotopyEquiv
    (blockOutgoingComplex a b c d e he) (schurOutgoingComplex a b c d e he) where
  hom := blockOutgoingProjection a b c d e he
  inv := blockOutgoingInclusion a b c d e he
  homotopyHomInvId := blockOutgoing_contraction a b c d e he
  homotopyInvHomId := ShortComplex.Homotopy.ofEq
    (blockOutgoing_inclusion_projection a b c d e he)

def blockOutgoingHomologyIso : (blockOutgoingComplex a b c d e he).homology ≅
    (schurOutgoingComplex a b c d e he).homology where
  hom := ShortComplex.homologyMap (blockOutgoingProjection a b c d e he)
  inv := ShortComplex.homologyMap (blockOutgoingInclusion a b c d e he)
  hom_inv_id := by
    rw [← ShortComplex.homologyMap_comp,
      (blockOutgoing_contraction a b c d e he).homologyMap_congr,
      ShortComplex.homologyMap_id]
  inv_hom_id := by
    rw [← ShortComplex.homologyMap_comp, blockOutgoing_inclusion_projection,
      ShortComplex.homologyMap_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianShortComplex.LocalSectionLifting
