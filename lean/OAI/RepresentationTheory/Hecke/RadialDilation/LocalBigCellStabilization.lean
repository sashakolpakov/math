import OAI.RepresentationTheory.Hecke.RadialDilation.LocalLeviStabilization
import OAI.RepresentationTheory.Weil.Local.GenerationSymplectic

/-! # Local Big Cell Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalBigCellStabilization.Realization

noncomputable section

section

/-! Opposite unipotent generators are locally finite on actual test vectors by Weyl conjugation. -/

open scoped Classical _root_.Topology
open Filter OAI.RepresentationTheory.Weil.Local.GenerationSymplectic.Construction

theorem linear_action_conjugation_apply {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : G →* (V ≃ₗ[ℂ] V)) (w g : G) (f : V) :
    ρ (w * g * w⁻¹) (ρ w f) = ρ w (ρ g f) := by
  have hc : ρ w⁻¹ (ρ w f) = f := by
    change (ρ w⁻¹ * ρ w) f = f
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [map_mul, map_mul]
  change ρ w (ρ g (ρ w⁻¹ (ρ w f))) = _
  rw [hc]

variable (q n : ℕ) [Fact q.Prime]
local instance c410LocalUpperStabilization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalUpperStabilization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem local_upper_conjugation (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) :
    Weil.Local.Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ =
      Weil.Local.Generators.Construction.weylSymplectic ℚ_[q] n * Weil.Local.GenerationSymplectic.Construction.upperSymplectic B * (Weil.Local.Generators.Construction.weylSymplectic ℚ_[q] n)⁻¹ := by
  simpa only [neg_neg] using Weil.Local.GenerationSymplectic.Construction.quadratic_upper_conjugation (k := ℚ_[q]) ⟨-B.val, B.property.neg⟩

theorem eventually_local_upper_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    ∀ᶠ B : Matrix (Fin n) (Fin n) ℚ_[q] in 𝓝 0,
      ∀ (hB : B.IsSymm) (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ),
        Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.GenerationSymplectic.Construction.upperSymplectic ⟨B, hB⟩ →
        ∃ ξ : ℂ, ξ ^ 2 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
  obtain ⟨_, _, _, _, _, _, _, w, _, _, hw, _, _, _, _⟩ :=
    hLocalWeil ℚ_[q] (LocalLiftChoice.Realization.padic_not_discrete q) n hn ψ hψ hunit hnontrivial
  let ρ := Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ
  have hquad := LocalLeviStabilization.Realization.eventually_local_quadratic_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial (ρ w f)
  have hneg : Tendsto (fun B : Matrix (Fin n) (Fin n) ℚ_[q] => -B) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0 : Matrix (Fin n) (Fin n) ℚ_[q]))
  filter_upwards [hneg.eventually hquad] with B hBquad
  intro hB g hg
  have hproj : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ (w * g * w⁻¹) =
      Weil.Local.Generators.Construction.quadraticSymplectic ⟨-B, hB.neg⟩ := by
    rw [map_mul, map_mul, map_inv, hw, hg]
    exact (local_upper_conjugation q n ⟨B, hB⟩).symm
  obtain ⟨ξ, hξ, hfix⟩ := hBquad hB.neg (w * g * w⁻¹) hproj
  refine ⟨ξ, hξ, ?_⟩
  apply (ρ w).injective
  rw [map_smul]
  exact (linear_action_conjugation_apply ρ w g f).symm.trans hfix

end

section

/-! Actual local Weil operators have finite-order phases on a neighborhood in symplectic block coordinates. -/

open scoped Classical _root_.Topology
open Filter OAI.RepresentationTheory.Weil.Local.GenerationSymplectic.Construction

theorem square_one_eighth_power {ξ : ℂ} (hξ : ξ ^ 2 = 1) : ξ ^ 8 = 1 := by
  calc
    _ = (ξ ^ 2) ^ 4 := by rw [← pow_mul]
    _ = 1 := by rw [hξ, one_pow]

variable (q n : ℕ) [Fact q.Prime]
local instance c410LocalBigCellStabilization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalBigCellStabilization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem local_bigCell_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n) (B C : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n)
    (hA : ∀ g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ, Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.Generators.Construction.leviSymplectic A →
      ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f)
    (hB : ∀ g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ, Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.GenerationSymplectic.Construction.upperSymplectic B →
      ∃ ξ : ℂ, ξ ^ 2 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f)
    (hC : ∀ g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ, Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.Generators.Construction.quadraticSymplectic C →
      ∃ ξ : ℂ, ξ ^ 2 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ)
    (hg : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.Generators.Construction.quadraticSymplectic C * Weil.Local.Generators.Construction.leviSymplectic A * Weil.Local.GenerationSymplectic.Construction.upperSymplectic B) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
  obtain ⟨_, _, _, _, hsurj, _, _, _, _, _, _, _, _, _, hcover⟩ :=
    hLocalWeil ℚ_[q] (LocalLiftChoice.Realization.padic_not_discrete q) n hn ψ hψ hunit hnontrivial
  obtain ⟨l, hl⟩ := hsurj (Weil.Local.Generators.Construction.quadraticSymplectic C)
  obtain ⟨m, hm⟩ := hsurj (Weil.Local.Generators.Construction.leviSymplectic A)
  obtain ⟨u, hu⟩ := hsurj (Weil.Local.GenerationSymplectic.Construction.upperSymplectic B)
  obtain ⟨ξl, hξl, hlf⟩ := hC l hl
  obtain ⟨ξm, hξm, hmf⟩ := hA m hm
  obtain ⟨ξu, hξu, huf⟩ := hB u hu
  have hp : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ (l * m * u) = Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g := by
    rw [map_mul, map_mul, hl, hm, hu, hg]
  obtain ⟨ε, hε, hεf⟩ := hcover (l * m * u) g hp
  refine ⟨ε * (ξu * (ξm * ξl)), ?_, ?_⟩
  · simp only [mul_pow, square_one_eighth_power hε, square_one_eighth_power hξu,
      square_one_eighth_power hξl, hξm, one_mul]
  · rw [hεf, map_mul, map_mul]
    change ε • (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ l
      (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ m (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ u f))) = _
    rw [huf, map_smul, hmf, map_smul, map_smul, hlf]
    simp only [smul_smul]

theorem eventually_local_bigCell_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    ∀ᶠ p : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n × (Matrix (Fin n) (Fin n) ℚ_[q] × Matrix (Fin n) (Fin n) ℚ_[q])
      in 𝓝 (1, (0, 0)),
      ∀ (hB : p.2.1.IsSymm) (hC : p.2.2.IsSymm) (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ),
        Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g =
          Weil.Local.Generators.Construction.quadraticSymplectic ⟨p.2.2, hC⟩ * Weil.Local.Generators.Construction.leviSymplectic p.1 * Weil.Local.GenerationSymplectic.Construction.upperSymplectic ⟨p.2.1, hB⟩ →
        ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
  let z : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n × (Matrix (Fin n) (Fin n) ℚ_[q] × Matrix (Fin n) (Fin n) ℚ_[q]) := (1, (0, 0))
  have hA := (continuous_fst.tendsto z).eventually
    (LocalLeviStabilization.Realization.eventually_local_levi_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial f)
  have hB := ((continuous_fst.comp continuous_snd).tendsto z).eventually
    (eventually_local_upper_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial f)
  have hC := ((continuous_snd.comp continuous_snd).tendsto z).eventually
    (LocalLeviStabilization.Realization.eventually_local_quadratic_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial f)
  filter_upwards [hA, hB, hC] with p hpA hpB hpC
  intro hB hC g hg
  exact local_bigCell_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial f p.1
    ⟨p.2.1, hB⟩ ⟨p.2.2, hC⟩ hpA (hpB hB) (hpC hC) g hg

end

/-! Continuous symplectic block coordinates on the open cell containing the identity. -/

open scoped Classical _root_.Topology _root_.Matrix
open Filter _root_.Matrix OAI.RepresentationTheory.Weil.Local.GenerationSymplectic.Construction

variable (q n : ℕ) [Fact q.Prime]

/-- The local symplectic group carries the subspace topology of its matrix entries. -/
instance padicSymplecticTopologicalSpace : TopologicalSpace (Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n) :=
  TopologicalSpace.induced Subtype.val inferInstance

theorem padicSymplectic_continuous_val :
    Continuous (fun g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n => g.val) := continuous_induced_dom

abbrev LocalBigCell := {g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n // g.val.toBlocks₁₁.det ≠ 0}

theorem localSymplectic_one_topLeft : (1 : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n).val.toBlocks₁₁ = 1 := by
  apply Matrix.ext
  intro i j
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

def localBigCellOne : LocalBigCell q n := ⟨1, by rw [localSymplectic_one_topLeft]; simp⟩

def localBigCellA (g : LocalBigCell q n) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n :=
  Matrix.nonsingInvUnit g.val.val.toBlocks₁₁ (isUnit_iff_ne_zero.mpr g.property)

theorem localBigCellA_val (g : LocalBigCell q n) : (localBigCellA q n g).val = g.val.val.toBlocks₁₁ := rfl

theorem localBigCellA_inv_val (g : LocalBigCell q n) :
    ((localBigCellA q n g)⁻¹).val = g.val.val.toBlocks₁₁⁻¹ := rfl

theorem localBigCell_continuous_entry (i j : Fin n ⊕ Fin n) :
    Continuous (fun g : LocalBigCell q n => g.val.val i j) := by
  have hbc : Continuous (fun g : LocalBigCell q n => g.val) := continuous_subtype_val
  exact (continuous_apply j).comp ((continuous_apply i).comp ((padicSymplectic_continuous_val q n).comp hbc))

theorem localBigCellA_continuous : Continuous (localBigCellA q n) := by
  have hA : Continuous (fun g : LocalBigCell q n => g.val.val.toBlocks₁₁) := by
    change Continuous (fun g : LocalBigCell q n => fun i j => g.val.val (Sum.inl i) (Sum.inl j))
    exact continuous_pi (fun i => continuous_pi (fun j => localBigCell_continuous_entry q n _ _))
  have hInv : Continuous (fun g : LocalBigCell q n => g.val.val.toBlocks₁₁⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    have hR : ContinuousAt Ring.inverse g.val.val.toBlocks₁₁.det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ g.property
    exact ContinuousAt.comp (f := fun h : LocalBigCell q n => h.val.val.toBlocks₁₁) (x := g)
      (continuousAt_matrix_inv g.val.val.toBlocks₁₁ hR) hA.continuousAt
  apply Units.continuous_iff.mpr
  exact ⟨hA, hInv⟩

def localBigCellParameters (g : LocalBigCell q n) :
    Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n × (Matrix (Fin n) (Fin n) ℚ_[q] × Matrix (Fin n) (Fin n) ℚ_[q]) :=
  (localBigCellA q n g,
    (((localBigCellA q n g)⁻¹).val * g.val.val.toBlocks₁₂,
      g.val.val.toBlocks₂₁ * ((localBigCellA q n g)⁻¹).val))

theorem localBigCellParameters_continuous : Continuous (localBigCellParameters q n) := by
  have hA := localBigCellA_continuous q n
  have hi : Continuous (fun g : LocalBigCell q n => ((localBigCellA q n g)⁻¹).val) :=
    Units.continuous_coe_inv.comp hA
  have hB : Continuous (fun g : LocalBigCell q n => g.val.val.toBlocks₁₂) := by
    change Continuous (fun g : LocalBigCell q n => fun i j => g.val.val (Sum.inl i) (Sum.inr j))
    exact continuous_pi (fun i => continuous_pi (fun j => localBigCell_continuous_entry q n _ _))
  have hC : Continuous (fun g : LocalBigCell q n => g.val.val.toBlocks₂₁) := by
    change Continuous (fun g : LocalBigCell q n => fun i j => g.val.val (Sum.inr i) (Sum.inl j))
    exact continuous_pi (fun i => continuous_pi (fun j => localBigCell_continuous_entry q n _ _))
  exact hA.prodMk ((hi.mul hB).prodMk (hC.mul hi))

theorem localBigCellA_one : localBigCellA q n (localBigCellOne q n) = 1 := by
  apply Units.ext
  rw [localBigCellA_val]
  exact localSymplectic_one_topLeft q n

theorem localBigCellParameters_one : localBigCellParameters q n (localBigCellOne q n) = (1, (0, 0)) := by
  have hB : (1 : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n).val.toBlocks₁₂ = 0 := by
    apply Matrix.ext
    intro i j
    simp [Matrix.toBlocks₁₂]
  have hC : (1 : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n).val.toBlocks₂₁ = 0 := by
    apply Matrix.ext
    intro i j
    simp [Matrix.toBlocks₂₁]
  dsimp only [localBigCellParameters]
  rw [localBigCellA_one]
  change (1, (((1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n)⁻¹).val * (1 : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n).val.toBlocks₁₂,
    (1 : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n).val.toBlocks₂₁ * ((1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n)⁻¹).val)) = _
  rw [hB, hC, mul_zero, zero_mul]

theorem localBigCell_parameters_symmetric (g : LocalBigCell q n) :
    (localBigCellParameters q n g).2.1.IsSymm ∧ (localBigCellParameters q n g).2.2.IsSymm := by
  have hg : Matrix.fromBlocks (localBigCellA q n g).val g.val.val.toBlocks₁₂
      g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂ ∈ Matrix.symplecticGroup (Fin n) ℚ_[q] := by
    rw [localBigCellA_val, Matrix.fromBlocks_toBlocks]
    exact g.val.property
  have h := Weil.Local.GenerationSymplectic.Construction.symplectic_bigCell_parameters_symmetric (localBigCellA q n g)
    g.val.val.toBlocks₁₂ g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂ hg
  exact ⟨h.2, h.1⟩

theorem localBigCell_factorization (g : LocalBigCell q n) :
    g.val = Weil.Local.Generators.Construction.quadraticSymplectic ⟨(localBigCellParameters q n g).2.2, (localBigCell_parameters_symmetric q n g).2⟩ *
      Weil.Local.Generators.Construction.leviSymplectic (localBigCellParameters q n g).1 *
      Weil.Local.GenerationSymplectic.Construction.upperSymplectic ⟨(localBigCellParameters q n g).2.1, (localBigCell_parameters_symmetric q n g).1⟩ := by
  have hg : Matrix.fromBlocks (localBigCellA q n g).val g.val.val.toBlocks₁₂
      g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂ ∈ Matrix.symplecticGroup (Fin n) ℚ_[q] := by
    rw [localBigCellA_val, Matrix.fromBlocks_toBlocks]
    exact g.val.property
  have h := Weil.Local.GenerationSymplectic.Construction.symplectic_bigCell_factorization (localBigCellA q n g)
    g.val.val.toBlocks₁₂ g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂ hg
  have heq : (⟨Matrix.fromBlocks (localBigCellA q n g).val g.val.val.toBlocks₁₂
      g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂, hg⟩ : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n) = g.val := by
    apply Subtype.ext
    change Matrix.fromBlocks (localBigCellA q n g).val g.val.val.toBlocks₁₂
      g.val.val.toBlocks₂₁ g.val.val.toBlocks₂₂ = g.val.val
    rw [localBigCellA_val, Matrix.fromBlocks_toBlocks]
  rw [heq] at h
  exact h

theorem localBigCell_isOpen : IsOpen {g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n | g.val.toBlocks₁₁.det ≠ 0} :=
  isOpen_ne.preimage (by
    apply Continuous.matrix_det
    change Continuous (fun g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n => fun i j => g.val (Sum.inl i) (Sum.inl j))
    exact continuous_pi (fun i => continuous_pi (fun j =>
      (continuous_apply (Sum.inl j)).comp ((continuous_apply (Sum.inl i)).comp (padicSymplectic_continuous_val q n)))))

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalBigCellStabilization.Realization
