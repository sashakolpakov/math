import OAI.RepresentationTheory.Hecke.RadialDilation.Haar

/-! # Local Lift Choice -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization

noncomputable section

section

/-! LocalWeil's actual local Weil operator on the constructed radial subspace. -/

open scoped Classical _root_.Topology

variable (q : ℕ) [Fact q.Prime]

local instance c410LocalWeil_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalWeil_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem padic_not_discrete : ¬ DiscreteTopology ℚ_[q] := by
  intro h
  let : DiscreteTopology ℚ_[q] := h
  have ht := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := q))
  have hzero : {0} ∈ 𝓝 (0 : ℚ_[q]) := (isOpen_discrete {0}).mem_nhds (by simp)
  have he := ht.eventually hzero
  obtain ⟨n, hn⟩ := he.exists
  exact pow_ne_zero n (Haar.Realization.uniformizerUnit q).ne_zero (Set.mem_singleton_iff.mp hn)

def scalarGL (a : ℚ_[q]ˣ) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] 3 :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) a

theorem scalarGL_determinant (a : ℚ_[q]ˣ) :
    Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] (scalarGL q a) = a ^ 3 := by
  apply Units.ext
  change Matrix.det (Matrix.scalar (Fin 3) (a : ℚ_[q])) = (a : ℚ_[q]) ^ 3
  simp [Matrix.scalar_apply, Matrix.det_diagonal]

theorem scalarGL_inverse_substitution (a : ℚ_[q]ˣ) (x : Mem.Realization.Position q) :
    Matrix.mulVec (↑((scalarGL q a)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]) x =
      fun i => (a : ℚ_[q])⁻¹ * x i := by
  have hm : (↑((scalarGL q a)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]) =
      Matrix.diagonal (fun _ : Fin 3 => (a : ℚ_[q])⁻¹) := by
    let au : (Fin 3 → ℚ_[q])ˣ :=
      ⟨(fun _ => (a : ℚ_[q])), (fun _ => (a : ℚ_[q])⁻¹),
        by ext; simp, by ext; simp⟩
    simp [scalarGL, Matrix.scalar_apply, Matrix.inv_diagonal]
    change ∀ i, (Ring.inverse (au : Fin 3 → ℚ_[q])) i = (a : ℚ_[q])⁻¹
    rw [Ring.inverse_unit]
    intro i
    rfl
  rw [hm]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

theorem scalarGL_modulus (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) :
    Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] (scalarGL q a)) = ‖(a : ℚ_[q])‖ ^ 3 := by
  rw [scalarGL_determinant]
  have hp : Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] (a ^ 3) = (Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] a) ^ 3 := by
    simp [Weil.Local.FunctionsMetaplectic.Construction.localModulus, map_pow]
  rw [hp, Haar.Realization.haarModulus_of_norm q a M ha]

/-- The actual LocalWeil lift realizes RadialDilation's split-place substitution; the
remaining scalar is an eighth root of unity, not a splitting character. -/
theorem localWeil_radial_substitution
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (ψ : AddChar ℚ_[q] ℂ)
    (hContinuous : Continuous (fun t : ℚ_[q] => ψ t))
    (hUnitary : ∀ t : ℚ_[q], ‖ψ t‖ = 1)
    (hNontrivial : ∃ t : ℚ_[q], ψ t ≠ 1)
    (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) :
    ∃ (lift : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 ψ) (ξ : ℂ),
      Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 ψ lift = Weil.Local.Generators.Construction.leviSymplectic (scalarGL q a) ∧
      ξ ^ 8 = 1 ∧
      (∀ b : Cm.radialInput q,
        Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ lift (Mem.Realization.radialSchwartzEmbedding q b) =
          ξ • Mem.Realization.radialSchwartzEmbedding q
            (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b)) ∧
      (∀ (b : Cm.radialInput q) (x : Mem.Realization.Position q),
        (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ lift (Mem.Realization.radialSchwartzEmbedding q b)).val x =
          ξ * (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
            b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i)) := by
  obtain ⟨_, _, hgaussian, _, _, m, u, w, hm, _, _, hlinear, _, _, _⟩ :=
    hLocalWeil ℚ_[q] (padic_not_discrete q) 3 (by decide) ψ hContinuous hUnitary hNontrivial
  let A := scalarGL q a
  let ξ := Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℚ_[q] ψ (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A) / Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℚ_[q] ψ 1
  have hphase : ξ ^ 8 = 1 := Weil.Local.Generators.Construction.index_ratio_eighth_power ℚ_[q] ψ _
    (hgaussian _ (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A).ne_zero).2.2 (hgaussian 1 one_ne_zero).2.2
  have hoperator (b : Cm.radialInput q) :
      Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ (m A) (Mem.Realization.radialSchwartzEmbedding q b) =
        ξ • Mem.Realization.radialSchwartzEmbedding q
          (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) := by
    apply Subtype.ext
    funext x
    rw [hlinear]
    change ξ * ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A)))⁻¹ : ℂ) *
      b.val (Matrix.mulVec (↑(A⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]) x) = _
    rw [scalarGL_modulus q a M ha, scalarGL_inverse_substitution]
    change ξ * ((Real.sqrt (‖(a : ℚ_[q])‖ ^ 3))⁻¹ : ℂ) *
      b.val (fun i => (a : ℚ_[q])⁻¹ * x i) =
        ξ * (((Real.sqrt (‖(a : ℚ_[q])‖ ^ 3))⁻¹ : ℂ) *
          b.val (fun i => (a : ℚ_[q])⁻¹ * x i))
    ring
  refine ⟨m A, ξ, hm A, hphase, hoperator, ?_⟩
  intro b x
  rw [hoperator]
  change ξ * (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b).val x = _
  rw [Mem.Realization.normalizedScalarSubstitution_apply]
  ring

end

/-! The radial calculation holds for every lift of the split scalar. -/

open scoped Classical _root_.Topology

variable (q : ℕ) [Fact q.Prime]
local instance c410LocalLiftChoice_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalLiftChoice_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem every_local_lift_radial_substitution
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (ψ : AddChar ℚ_[q] ℂ)
    (hContinuous : Continuous (fun t : ℚ_[q] => ψ t))
    (hUnitary : ∀ t : ℚ_[q], ‖ψ t‖ = 1)
    (hNontrivial : ∃ t : ℚ_[q], ψ t ≠ 1)
    (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ)))
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 ψ)
    (hg : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 ψ g = Weil.Local.Generators.Construction.leviSymplectic (scalarGL q a)) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧
      ∀ b : Cm.radialInput q,
        Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ g (Mem.Realization.radialSchwartzEmbedding q b) =
          ξ • Mem.Realization.radialSchwartzEmbedding q (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) := by
  obtain ⟨lift, ξ₀, hp, hξ₀, hop, _⟩ := localWeil_radial_substitution q
    hLocalWeil ψ hContinuous hUnitary hNontrivial a M ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcover⟩ :=
    hLocalWeil ℚ_[q] (padic_not_discrete q) 3 (by decide) ψ hContinuous hUnitary hNontrivial
  obtain ⟨ε, hε, hεop⟩ := hcover lift g (hp.trans hg.symm)
  have hε₈ : ε ^ 8 = 1 := by
    calc
      _ = (ε ^ 2) ^ 4 := by rw [← pow_mul]
      _ = 1 := by rw [hε, one_pow]
  refine ⟨ε * ξ₀, ?_, ?_⟩
  · rw [mul_pow, hε₈, hξ₀, mul_one]
  · intro b
    rw [hεop, hop, smul_smul]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization
