import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianShortComplex

/-! # Gaussian Incoming Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianIncomingComplex.LocalSectionLifting

noncomputable section

/-! Gaussian cancellation for the incoming differential of a short complex. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
    {A B C D E : Type v}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    [AddCommGroup E] [Module R E]
    (a : A →ₗ[R] C) (b : B →ₗ[R] C) (c : A →ₗ[R] D) (d : B ≃ₗ[R] D)
    (e : (C × D) →ₗ[R] E) (he : e.comp (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d) = 0)

abbrev blockIncomingComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d) e he

include he in
theorem schurIncoming_zero :
    (e.comp (LinearMap.inl R C D)).comp (ComplexGaussian.LocalSectionLifting.schurDifferential a b c d) = 0 := by
  apply LinearMap.ext
  intro x
  change e (ComplexGaussian.LocalSectionLifting.schurDifferential a b c d x, 0) = 0
  rw [← GaussianContraction.LocalSectionLifting.block_differential_inclusion a b c d x]
  exact LinearMap.congr_fun he (GaussianContraction.LocalSectionLifting.blockSourceInclusion c d x)

abbrev schurIncomingComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (ComplexGaussian.LocalSectionLifting.schurDifferential a b c d) (e.comp (LinearMap.inl R C D))
    (schurIncoming_zero a b c d e he)

include he in
theorem block_target_retraction_after_differential (x : C × D) :
    e (GaussianCokernel.LocalSectionLifting.blockCokernelProjection b d x, 0) = e x := by
  rw [GaussianContraction.LocalSectionLifting.block_target_contraction a b c d x, map_sub]
  have hx : e (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d (GaussianContraction.LocalSectionLifting.blockContractingMap d x)) = 0 :=
    LinearMap.congr_fun he (GaussianContraction.LocalSectionLifting.blockContractingMap d x)
  rw [hx, sub_zero]

def blockIncomingProjection : blockIncomingComplex a b c d e he ⟶
    schurIncomingComplex a b c d e he where
  τ₁ := ModuleCat.ofHom (LinearMap.fst R A B)
  τ₂ := ModuleCat.ofHom (GaussianCokernel.LocalSectionLifting.blockCokernelProjection b d)
  τ₃ := 𝟙 _
  comm₁₂ := by
    ext x
    exact (GaussianContraction.LocalSectionLifting.block_projection_differential a b c d x).symm
  comm₂₃ := by
    ext x
    exact block_target_retraction_after_differential a b c d e he x

def blockIncomingInclusion : schurIncomingComplex a b c d e he ⟶
    blockIncomingComplex a b c d e he where
  τ₁ := ModuleCat.ofHom (GaussianContraction.LocalSectionLifting.blockSourceInclusion c d)
  τ₂ := ModuleCat.ofHom (LinearMap.inl R C D)
  τ₃ := 𝟙 _
  comm₁₂ := by
    ext x
    exact GaussianContraction.LocalSectionLifting.block_differential_inclusion a b c d x
  comm₂₃ := rfl

theorem blockIncoming_inclusion_projection :
    blockIncomingInclusion a b c d e he ≫ blockIncomingProjection a b c d e he =
      𝟙 (schurIncomingComplex a b c d e he) := by
  apply ShortComplex.Hom.ext
  · ext x
    exact GaussianContraction.LocalSectionLifting.block_source_retraction c d x
  · ext x
    exact GaussianContraction.LocalSectionLifting.block_target_retraction b d x
  · rfl

def blockIncoming_contraction : ShortComplex.Homotopy
    (blockIncomingProjection a b c d e he ≫ blockIncomingInclusion a b c d e he)
    (𝟙 (blockIncomingComplex a b c d e he)) where
  h₀ := 0
  h₁ := ModuleCat.ofHom (-GaussianContraction.LocalSectionLifting.blockContractingMap d)
  h₂ := 0
  h₃ := 0
  h₀_f := by
    ext x
    exact map_zero (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d)
  g_h₃ := by ext x; rfl
  comm₁ := by
    ext x
    change A × B at x
    change GaussianContraction.LocalSectionLifting.blockSourceInclusion c d x.1 =
      -GaussianContraction.LocalSectionLifting.blockContractingMap d (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d x) + 0 + x
    rw [GaussianContraction.LocalSectionLifting.block_source_contraction a b c d x]
    abel
  comm₂ := by
    ext x
    change C × D at x
    change (GaussianCokernel.LocalSectionLifting.blockCokernelProjection b d x, (0 : D)) =
      0 + ComplexGaussian.LocalSectionLifting.blockDifferential a b c d (-GaussianContraction.LocalSectionLifting.blockContractingMap d x) + x
    rw [GaussianContraction.LocalSectionLifting.block_target_contraction a b c d x, map_neg]
    abel
  comm₃ := by
    ext x
    change E at x
    change x = (0 : E) + e 0 + x
    simp

def blockIncomingHomotopyEquiv : ShortComplex.HomotopyEquiv
    (blockIncomingComplex a b c d e he) (schurIncomingComplex a b c d e he) where
  hom := blockIncomingProjection a b c d e he
  inv := blockIncomingInclusion a b c d e he
  homotopyHomInvId := blockIncoming_contraction a b c d e he
  homotopyInvHomId := ShortComplex.Homotopy.ofEq
    (blockIncoming_inclusion_projection a b c d e he)

def blockIncomingHomologyIso : (blockIncomingComplex a b c d e he).homology ≅
    (schurIncomingComplex a b c d e he).homology where
  hom := ShortComplex.homologyMap (blockIncomingProjection a b c d e he)
  inv := ShortComplex.homologyMap (blockIncomingInclusion a b c d e he)
  hom_inv_id := by
    rw [← ShortComplex.homologyMap_comp,
      (blockIncoming_contraction a b c d e he).homologyMap_congr,
      ShortComplex.homologyMap_id]
  inv_hom_id := by
    rw [← ShortComplex.homologyMap_comp, blockIncoming_inclusion_projection,
      ShortComplex.homologyMap_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianIncomingComplex.LocalSectionLifting
