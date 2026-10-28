import OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameOf

/-! # Mahler Frame Normed -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameNormed.Construction

noncomputable section

section

/-! Transport of matrix-frame actions and integral stabilizers through a
real linear change of ambient vector space. -/

open scoped Classical
open _root_.Module

theorem matrixFrameAction_transport
    {E F I : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [Fintype I] [DecidableEq I] (b : Basis I ℝ E) (e : E ≃ₗ[ℝ] F)
    (g : Matrix.GeneralLinearGroup I ℝ) (x : E) :
    e (LatticeFrameAction.Construction.matrixFrameAction b g x) = LatticeFrameAction.Construction.matrixFrameAction (b.map e) g (e x) := by
  have he : e.toLinearMap.comp (LatticeFrameAction.Construction.matrixFrameAction b g).toLinearMap =
      (LatticeFrameAction.Construction.matrixFrameAction (b.map e) g).toLinearMap.comp e.toLinearMap := by
    apply b.ext
    intro i
    change e (Matrix.toLin b b g.val (b i)) =
      Matrix.toLin (b.map e) (b.map e) g.val ((b.map e) i)
    rw [Matrix.toLin_self, Matrix.toLin_self, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, Basis.map_apply]
  exact LinearMap.congr_fun he x

theorem matrixFrameAction_transport_inverse
    {E F I : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [Fintype I] [DecidableEq I] (b : Basis I ℝ E) (e : F ≃ₗ[ℝ] E)
    (g : Matrix.GeneralLinearGroup I ℝ) (y : F) :
    e (LatticeFrameAction.Construction.matrixFrameAction (b.map e.symm) g y) = LatticeFrameAction.Construction.matrixFrameAction b g (e y) := by
  have he := congrArg e (matrixFrameAction_transport b e.symm g (e y))
  simpa only [e.apply_symm_apply, e.symm_apply_apply] using he.symm

theorem matrixFrameIntegralStabilizer_comap
    {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype I] [DecidableEq I] (Λ : Submodule ℤ E) (b : Basis I ℝ E) (e : F ≃L[ℝ] E) :
    SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.map e.symm.toLinearEquiv))
        (ZLattice.comap ℝ Λ e.toLinearMap) =
      SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ := by
  ext g
  simp only [StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff]
  change (∀ y : F, e (LatticeFrameAction.Construction.matrixFrameAction (b.map e.symm.toLinearEquiv) g y) ∈ Λ ↔ e y ∈ Λ) ↔
    ∀ x : E, LatticeFrameAction.Construction.matrixFrameAction b g x ∈ Λ ↔ x ∈ Λ
  have ht (y : F) : e (LatticeFrameAction.Construction.matrixFrameAction (b.map e.symm.toLinearEquiv) g y) =
      LatticeFrameAction.Construction.matrixFrameAction b g (e y) := matrixFrameAction_transport_inverse b e.toLinearEquiv g y
  simp_rw [ht]
  constructor
  · intro h x
    simpa only [e.apply_symm_apply] using h (e.symm x)
  · intro h y
    exact h (e y)

end

section

/-! Mahler compactness for an arbitrary finite-dimensional real normed
space, obtained by transporting the inner-product-space theorem through
a fixed Euclidean coordinate equivalence. -/

open scoped Classical
open _root_.Module Set _root_.MeasureTheory

def euclideanCoordinateEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : EuclideanSpace ℝ (Fin (finrank ℝ E)) ≃L[ℝ] E :=
  (EuclideanSpace.equiv (Fin (finrank ℝ E)) ℝ).trans
    (Module.finBasis ℝ E).equivFun.symm.toContinuousLinearEquiv

theorem exists_compact_special_lattice_representatives_dimEq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {m : ℕ} (hm : finrank ℝ F = m)
    (Λ : Submodule ℤ F) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin m) ℤ Λ) (μ : Measure F) [Measure.IsAddHaarMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (Matrix.SpecialLinearGroup (Fin m) ℝ), IsCompact K ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin m) ℝ,
        (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (b.ofZLatticeBasis ℝ) g.toGL x‖) →
        ∃ γ ∈ (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ).comap
          Matrix.SpecialLinearGroup.toGL, g * γ ∈ K := by
  subst m
  exact MahlerFrameOf.Construction.exists_compact_special_lattice_representatives Λ b μ ε hε

theorem mahler_compactness_normed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin (finrank ℝ E)) ℤ Λ) (ε : ℝ) (hε : 0 < ε) :
    let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ).comap
      Matrix.SpecialLinearGroup.toGL
    IsCompact ((QuotientGroup.mk : Matrix.SpecialLinearGroup (Fin (finrank ℝ E)) ℝ →
      Matrix.SpecialLinearGroup (Fin (finrank ℝ E)) ℝ ⧸ Γ) ''
      {g | ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (b.ofZLatticeBasis ℝ) g.toGL x‖}) := by
  let F := EuclideanSpace ℝ (Fin (finrank ℝ E))
  let e : F ≃L[ℝ] E := euclideanCoordinateEquiv E
  let Ω := ZLattice.comap ℝ Λ e.toLinearMap
  let B := b.ofZLatticeComap ℝ Λ e.toLinearEquiv
  let b₀ := b.ofZLatticeBasis ℝ
  let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b₀) Λ).comap Matrix.SpecialLinearGroup.toGL
  let δ := ε / (‖e.toContinuousLinearMap‖ + 1)
  have hC : 0 < ‖e.toContinuousLinearMap‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hC
  have hB : B.ofZLatticeBasis ℝ = b₀.map e.symm.toLinearEquiv := b.ofZLatticeBasis_comap ℝ Λ e
  have hΓ : (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (B.ofZLatticeBasis ℝ)) Ω).comap
      Matrix.SpecialLinearGroup.toGL = Γ := by
    rw [hB, matrixFrameIntegralStabilizer_comap]
  obtain ⟨K, hK, hrep⟩ := exists_compact_special_lattice_representatives_dimEq
    (F := F) (by simp [F]) Ω B volume δ hδ
  let S : Set (Matrix.SpecialLinearGroup (Fin (finrank ℝ E)) ℝ) :=
    {g | ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction b₀ g.toGL x‖}
  refine MahlerFrameOf.Construction.compact_quotient_image_of_representatives Γ S K ?_ hK ?_ ?_
  · simp only [S, Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    apply isClosed_iInter
    intro _
    exact isClosed_le continuous_const
      (((MahlerFrameOf.Construction.continuous_matrixFrameAction b₀ x).comp Matrix.SpecialLinearGroup.continuous_toGL).norm)
  · intro g hg γ hγ x hx hx0
    have hxmem : LatticeFrameAction.Construction.matrixFrameAction b₀ γ.toGL x ∈ Λ :=
      ((StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (LatticeFrameAction.Construction.matrixFrameIntegralAction b₀) Λ γ.toGL).mp hγ x).mpr hx
    have hxne : LatticeFrameAction.Construction.matrixFrameAction b₀ γ.toGL x ≠ 0 :=
      fun he => hx0 ((LatticeFrameAction.Construction.matrixFrameAction b₀ γ.toGL).injective (he.trans (map_zero _).symm))
    simpa only [map_mul, LinearEquiv.mul_apply] using hg (LatticeFrameAction.Construction.matrixFrameAction b₀ γ.toGL x) hxmem hxne
  · intro g hg
    have hgapF : ∀ y ∈ Ω, y ≠ 0 → δ ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g.toGL y‖ := by
      intro y hy hy0
      have hyne : e y ≠ 0 := fun he => hy0 (e.injective (he.trans (map_zero e).symm))
      have hgap := hg (e y) hy hyne
      have heq : e (LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g.toGL y) =
          LatticeFrameAction.Construction.matrixFrameAction b₀ g.toGL (e y) := by
        rw [hB]
        exact matrixFrameAction_transport_inverse b₀ e.toLinearEquiv g.toGL y
      rw [← heq] at hgap
      apply (div_le_iff₀ hC).mpr
      calc
        ε ≤ ‖e (LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g.toGL y)‖ := hgap
        _ ≤ ‖e.toContinuousLinearMap‖ * ‖LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g.toGL y‖ :=
          e.toContinuousLinearMap.le_opNorm _
        _ ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g.toGL y‖ * (‖e.toContinuousLinearMap‖ + 1) := by
          nlinarith [norm_nonneg (LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g.toGL y)]
    obtain ⟨γ, hγ, hγK⟩ := hrep g hgapF
    exact ⟨γ, hΓ ▸ hγ, hγK⟩

end

/-! Compact general-linear lattice representatives for arbitrary real
normed spaces, with absolute determinant one. -/

open scoped Classical
open _root_.Module Set _root_.MeasureTheory

theorem exists_compact_matrix_lattice_representatives_dimEq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {m : ℕ} (hm : finrank ℝ F = m)
    (Λ : Submodule ℤ F) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin m) ℤ Λ) (μ : Measure F) [Measure.IsAddHaarMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (Matrix.GeneralLinearGroup (Fin m) ℝ), IsCompact K ∧
      ∀ g : Matrix.GeneralLinearGroup (Fin m) ℝ, |g.val.det| = 1 →
        (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (b.ofZLatticeBasis ℝ) g x‖) →
        ∃ γ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ,
          g * γ ∈ K := by
  subst m
  exact LatticeFrameAction.Construction.exists_compact_matrix_lattice_representatives Λ b μ ε hε

theorem exists_compact_matrix_lattice_representatives_normed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin (finrank ℝ E)) ℤ Λ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (Matrix.GeneralLinearGroup (Fin (finrank ℝ E)) ℝ), IsCompact K ∧
      ∀ g : Matrix.GeneralLinearGroup (Fin (finrank ℝ E)) ℝ, |g.val.det| = 1 →
        (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (b.ofZLatticeBasis ℝ) g x‖) →
        ∃ γ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ,
          g * γ ∈ K := by
  let F := EuclideanSpace ℝ (Fin (finrank ℝ E))
  let e : F ≃L[ℝ] E := euclideanCoordinateEquiv E
  let Ω := ZLattice.comap ℝ Λ e.toLinearMap
  let B := b.ofZLatticeComap ℝ Λ e.toLinearEquiv
  let b₀ := b.ofZLatticeBasis ℝ
  let δ := ε / (‖e.toContinuousLinearMap‖ + 1)
  have hC : 0 < ‖e.toContinuousLinearMap‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hC
  have hB : B.ofZLatticeBasis ℝ = b₀.map e.symm.toLinearEquiv := b.ofZLatticeBasis_comap ℝ Λ e
  have hΓ : SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (B.ofZLatticeBasis ℝ)) Ω =
      SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b₀) Λ := by
    rw [hB, matrixFrameIntegralStabilizer_comap]
  obtain ⟨K, hK, hrep⟩ := exists_compact_matrix_lattice_representatives_dimEq
    (F := F) (by simp [F]) Ω B volume δ hδ
  refine ⟨K, hK, fun g hg hgap => ?_⟩
  have hgapF : ∀ y ∈ Ω, y ≠ 0 → δ ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g y‖ := by
    intro y hy hy0
    have hyne : e y ≠ 0 := fun he => hy0 (e.injective (he.trans (map_zero e).symm))
    have h := hgap (e y) hy hyne
    have heq : e (LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g y) = LatticeFrameAction.Construction.matrixFrameAction b₀ g (e y) := by
      rw [hB]
      exact matrixFrameAction_transport_inverse b₀ e.toLinearEquiv g y
    rw [← heq] at h
    apply (div_le_iff₀ hC).mpr
    calc
      ε ≤ ‖e (LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g y)‖ := h
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g y‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g y‖ * (‖e.toContinuousLinearMap‖ + 1) := by
        nlinarith [norm_nonneg (LatticeFrameAction.Construction.matrixFrameAction (B.ofZLatticeBasis ℝ) g y)]
  obtain ⟨γ, hγ, hγK⟩ := hrep g hg hgapF
  exact ⟨γ, hΓ ▸ hγ, hγK⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameNormed.Construction
