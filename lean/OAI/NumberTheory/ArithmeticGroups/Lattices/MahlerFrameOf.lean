import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeFrameAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.CovolumeTransport

/-! # Mahler Frame Of -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameOf.Construction

noncomputable section

section

/-! Orientation correction gives Mahler representatives in the special
linear group itself. -/

open scoped Classical
open Set _root_.Module _root_.MeasureTheory

theorem special_linear_compact_representatives_of_general
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι ℝ))
    (hΓ : ∀ γ ∈ Γ, |γ.val.det| = 1)
    (P : Matrix.SpecialLinearGroup ι ℝ → Prop)
    (K : Set (Matrix.GeneralLinearGroup ι ℝ)) (hK : IsCompact K)
    (hcover : ∀ g, P g → ∃ γ ∈ Γ, g.toGL * γ ∈ K) :
    ∃ C : Set (Matrix.SpecialLinearGroup ι ℝ), IsCompact C ∧
      ∀ g, P g → ∃ γ ∈ Γ.comap Matrix.SpecialLinearGroup.toGL, g * γ ∈ C := by
  have hcorrect : ∃ D : Set (Matrix.GeneralLinearGroup ι ℝ), IsCompact D ∧
      ∀ g, P g → ∃ γ ∈ Γ, γ.val.det = 1 ∧ g.toGL * γ ∈ D := by
    by_cases hall : ∀ γ ∈ Γ, γ.val.det = 1
    · refine ⟨K, hK, fun g hg => ?_⟩
      obtain ⟨γ, hγ, hγK⟩ := hcover g hg
      exact ⟨γ, hγ, hall γ hγ, hγK⟩
    · push Not at hall
      obtain ⟨τ, hτ, hτne⟩ := hall
      have hτdet : τ.val.det = -1 := (eq_or_eq_neg_of_abs_eq (hΓ τ hτ)).resolve_left hτne
      refine ⟨K ∪ (fun M => M * τ) '' K,
        hK.union (hK.image (continuous_id.mul continuous_const)), fun g hg => ?_⟩
      obtain ⟨γ, hγ, hγK⟩ := hcover g hg
      rcases eq_or_eq_neg_of_abs_eq (hΓ γ hγ) with hγdet | hγdet
      · exact ⟨γ, hγ, hγdet, Or.inl hγK⟩
      · refine ⟨γ * τ, Γ.mul_mem hγ hτ, ?_, Or.inr ?_⟩
        · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hγdet, hτdet]
          norm_num
        · exact ⟨g.toGL * γ, hγK, mul_assoc _ _ _⟩
  obtain ⟨D, hD, hDcover⟩ := hcorrect
  refine ⟨Matrix.SpecialLinearGroup.toGL ⁻¹' D,
    Matrix.SpecialLinearGroup.isClosedEmbedding_toGL.isCompact_preimage hD, ?_⟩
  intro g hg
  obtain ⟨γ, hγ, hγdet, hγD⟩ := hDcover g hg
  let δ : Matrix.SpecialLinearGroup ι ℝ := ⟨γ.val, hγdet⟩
  have hδ : δ.toGL = γ := Units.ext rfl
  refine ⟨δ, ?_, ?_⟩
  · change δ.toGL ∈ Γ
    rwa [hδ]
  · change (g * δ).toGL ∈ D
    simpa only [map_mul, hδ] using hγD

theorem exists_compact_special_lattice_representatives
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin (finrank ℝ E)) ℤ Λ)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (Matrix.SpecialLinearGroup (Fin (finrank ℝ E)) ℝ), IsCompact K ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin (finrank ℝ E)) ℝ,
        (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (b.ofZLatticeBasis ℝ) g.toGL x‖) →
        ∃ γ ∈ (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ).comap
          Matrix.SpecialLinearGroup.toGL, g * γ ∈ K := by
  obtain ⟨K, hK, hrep⟩ := LatticeFrameAction.Construction.exists_compact_matrix_lattice_representatives Λ b μ ε hε
  apply special_linear_compact_representatives_of_general
    (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ)
    (fun _ hγ => CovolumeTransport.Construction.matrix_lattice_stabilizer_abs_det_one Λ μ (b.ofZLatticeBasis ℝ) hγ)
    _ K hK
  intro g hgap
  apply hrep g.toGL _ hgap
  change |g.val.det| = 1
  rw [g.property, abs_one]

end

section

/-! Mahler compactness in the quotient of the special linear group by
the stabilizer of a full integral lattice. -/

open scoped Classical
open Set _root_.Module _root_.MeasureTheory

theorem continuous_matrixFrameAction
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) (x : E) :
    Continuous (fun g : Matrix.GeneralLinearGroup ι ℝ => LatticeFrameAction.Construction.matrixFrameAction b g x) := by
  have he (g : Matrix.GeneralLinearGroup ι ℝ) :
      LatticeFrameAction.Construction.matrixFrameAction b g x = b.equivFun.symm (g.val.mulVec (b.repr x)) := by
    apply b.equivFun.injective
    rw [b.equivFun.apply_symm_apply]
    rw [Basis.equivFun_apply]
    change (b.repr ((LatticeFrameAction.Construction.matrixFrameAction b g).toLinearMap x) : ι → ℝ) = _
    rw [LatticeFrameAction.Construction.matrixFrameAction_toLinearMap]
    exact Matrix.repr_toLin b b g.val x
  simp_rw [he]
  exact b.equivFun.symm.continuous_of_finiteDimensional.comp
    (Units.continuous_val.matrix_mulVec continuous_const)

theorem compact_quotient_image_of_representatives
    {H : Type*} [Group H] [TopologicalSpace H]
    (Γ : Subgroup H) (S K : Set H) (hS : IsClosed S) (hK : IsCompact K)
    (hsat : ∀ g ∈ S, ∀ γ ∈ Γ, g * γ ∈ S)
    (hrep : ∀ g ∈ S, ∃ γ ∈ Γ, g * γ ∈ K) :
    IsCompact ((QuotientGroup.mk : H → H ⧸ Γ) '' S) := by
  have hpre : (QuotientGroup.mk : H → H ⧸ Γ) ⁻¹'
      ((QuotientGroup.mk : H → H ⧸ Γ) '' S) = S := by
    ext g
    constructor
    · rintro ⟨x, hx, he⟩
      have hγ : x⁻¹ * g ∈ Γ := QuotientGroup.eq.mp he
      simpa only [mul_inv_cancel_left] using hsat x hx (x⁻¹ * g) hγ
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hclosed : IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) '' S) := by
    rw [← (QuotientGroup.isQuotientMap_mk Γ).isClosed_preimage, hpre]
    exact hS
  apply (hK.image (QuotientGroup.continuous_mk (N := Γ))).of_isClosed_subset hclosed
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨γ, hγ, hγK⟩ := hrep g hg
  exact ⟨g * γ, hγK, QuotientGroup.mk_mul_of_mem g hγ⟩

theorem mahler_compactness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin (finrank ℝ E)) ℤ Λ)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ).comap
      Matrix.SpecialLinearGroup.toGL
    IsCompact ((QuotientGroup.mk : Matrix.SpecialLinearGroup (Fin (finrank ℝ E)) ℝ →
      Matrix.SpecialLinearGroup (Fin (finrank ℝ E)) ℝ ⧸ Γ) ''
      {g | ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction (b.ofZLatticeBasis ℝ) g.toGL x‖}) := by
  let b₀ := b.ofZLatticeBasis ℝ
  let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b₀) Λ).comap
    Matrix.SpecialLinearGroup.toGL
  let S : Set (Matrix.SpecialLinearGroup (Fin (finrank ℝ E)) ℝ) :=
    {g | ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction b₀ g.toGL x‖}
  obtain ⟨K, hK, hrep⟩ := exists_compact_special_lattice_representatives Λ b μ ε hε
  apply compact_quotient_image_of_representatives Γ S K _ hK _ hrep
  · simp only [S, Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    apply isClosed_iInter
    intro _
    exact isClosed_le continuous_const
      (((continuous_matrixFrameAction b₀ x).comp Matrix.SpecialLinearGroup.continuous_toGL).norm)
  · intro g hg γ hγ x hx hx0
    have hγmem : LatticeFrameAction.Construction.matrixFrameAction b₀ γ.toGL x ∈ Λ :=
      (StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (LatticeFrameAction.Construction.matrixFrameIntegralAction b₀) Λ γ.toGL).mp hγ x |>.mpr hx
    have hγ0 : LatticeFrameAction.Construction.matrixFrameAction b₀ γ.toGL x ≠ 0 := by
      intro he
      exact hx0 ((LatticeFrameAction.Construction.matrixFrameAction b₀ γ.toGL).injective (he.trans (map_zero _).symm))
    have h := hg (LatticeFrameAction.Construction.matrixFrameAction b₀ γ.toGL x) hγmem hγ0
    simpa only [map_mul, LinearEquiv.mul_apply] using h

end

/-! Discreteness of a full lattice stabilizer in matrix coordinates. -/

open scoped Classical
open Set _root_.Module

theorem matrix_frame_stabilizer_discrete
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
    DiscreteTopology (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ) := by
  let b₀ := b.ofZLatticeBasis ℝ
  let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b₀) Λ
  let f : Γ → (ι → Λ) := fun g i => ⟨LatticeFrameAction.Construction.matrixFrameAction b₀ g.val (b i).val, by
    exact (StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (LatticeFrameAction.Construction.matrixFrameIntegralAction b₀) Λ g.val).mp
      g.property (b i).val |>.mpr (b i).property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro i
    exact ((continuous_matrixFrameAction b₀ (b i).val).comp continuous_subtype_val).subtype_mk _
  · intro g h he
    apply Subtype.ext
    apply (LatticeFrameAction.Construction.matrixFrameAction b₀).injective
    apply b₀.ext'
    intro i
    have hi := congrArg (fun u : ι → Λ => (u i).val) he
    simpa only [f, b₀, Basis.ofZLatticeBasis_apply] using hi

theorem special_frame_stabilizer_discrete
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
    DiscreteTopology
      ((SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ).comap
        Matrix.SpecialLinearGroup.toGL) := by
  let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) Λ
  let : DiscreteTopology Γ := matrix_frame_stabilizer_discrete Λ b
  exact DiscreteTopology.preimage_of_continuous_injective (Γ : Set (Matrix.GeneralLinearGroup ι ℝ))
    Matrix.SpecialLinearGroup.continuous_toGL Matrix.SpecialLinearGroup.toGL_injective

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameOf.Construction
