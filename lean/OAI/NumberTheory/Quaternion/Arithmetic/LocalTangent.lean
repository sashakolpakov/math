import OAI.NumberTheory.Quaternion.Arithmetic.LocalExpIntegration
import OAI.NumberTheory.Quaternion.Arithmetic.LogTangent
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixOpenness
import OAI.NumberTheory.Quaternion.Arithmetic.TangentBracket

/-! # Local Tangent -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalTangent

noncomputable section

/-! The full local group's analytic tangent span over the closed prime
field is exactly its algebraic Lie algebra with scalars restricted. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Operator
open NormedSpace Set Filter _root_.Topology IsDedekindDomain

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem finite_infinitesimal_le_prime_tangentSpan (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange (K := v.adicCompletion F)
        G (LocalAdeles.localEmbedding (Sum.inr v)))).toSubmodule.restrictScalars
          (TangentBracket.closedPrimeSubfield (v.adicCompletion F))) ≤
      TangentBracket.matrixTangentSpanOver (K := v.adicCompletion F)
        (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)) G (LocalAdeles.localEmbedding (Sum.inr v)) ⊤ := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  let : @CompleteSpace (Matrix (Fin n) (Fin n) (v.adicCompletion F))
      (inferInstance : NormedRing (Matrix (Fin n) (Fin n) (v.adicCompletion F))).toUniformSpace :=
    FiniteDimensional.complete (v.adicCompletion F) _
  intro X hX
  let H := ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange (K := v.adicCompletion F) G (LocalAdeles.localEmbedding (Sum.inr v))
  have hlie : X ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer H := hX
  have hexp := LocalExpIntegration.local_infinitesimal_exp_eventually_mem
    (LocalCompletion.finite_expSeries_radius_pos v (Matrix (Fin n) (Fin n) (v.adicCompletion F))) H hlie
  have hball := LocalExpDerivative.local_exp_smul_eventually_mem_ball
    (LocalCompletion.finite_expSeries_radius_pos v (Matrix (Fin n) (Fin n) (v.adicCompletion F))) X
  let p : v.adicCompletion F := LocalCompletion.residuePrime v
  have hp : ‖p‖ < 1 := (LocalCompletion.natCast_norm_lt_one_iff v _).mpr dvd_rfl
  have hlim : Tendsto (fun j : ℕ => p ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp
  have hevent : ∀ᶠ j : ℕ in atTop,
      exp (p ^ j • X) ∈ range (fun g : H.RationalPoints =>
        (g.val : Matrix (Fin n) (Fin n) (v.adicCompletion F))) ∧
      p ^ j • X ∈ Metric.eball 0
        (expSeries (v.adicCompletion F) (Matrix (Fin n) (Fin n) (v.adicCompletion F))).radius :=
    hlim (hexp.and hball)
  obtain ⟨j, hjexp, hjball⟩ := hevent.exists
  let GM := (⊤ : Subgroup (LocalAdeles.LocalPoints G (Sum.inr v))).toSubmonoid.map (MatrixOpenness.localMatrixMonoidHom G v)
  have hmem : exp (p ^ j • X) ∈ GM := by
    obtain ⟨g, hg⟩ := hjexp
    exact ⟨g, by trivial, hg⟩
  have hcone := LogTangent.local_exp_parameter_mem_tangentCone v GM hjball hmem
  have hspan : p ^ j • X ∈ TangentBracket.matrixTangentSpanOver (K := v.adicCompletion F)
      (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)) G (LocalAdeles.localEmbedding (Sum.inr v)) ⊤ :=
    Submodule.subset_span hcone
  let a : TangentBracket.closedPrimeSubfield (v.adicCompletion F) := (LocalCompletion.residuePrime v : TangentBracket.closedPrimeSubfield _) ^ j
  have ha : a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (LocalCompletion.residuePrime_prime v).ne_zero)
  have he : p ^ j • X = a • X := rfl
  rw [he] at hspan
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using
    (TangentBracket.matrixTangentSpanOver (K := v.adicCompletion F)
      (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)) G (LocalAdeles.localEmbedding (Sum.inr v)) ⊤).smul_mem
        a⁻¹ hspan

theorem finite_prime_tangentSpan_eq_infinitesimal (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (hG : G.IsGeometricallyConnected) (v : HeightOneSpectrum (𝓞 F)) :
    TangentBracket.matrixTangentSpanOver (K := v.adicCompletion F)
        (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)) G (LocalAdeles.localEmbedding (Sum.inr v)) ⊤ =
      (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange (K := v.adicCompletion F)
        G (LocalAdeles.localEmbedding (Sum.inr v)))).toSubmodule.restrictScalars
          (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  apply le_antisymm
  · intro X hX
    have hm : X ∈ TangentCone.matrixTangentSpan (K := v.adicCompletion F)
        G (LocalAdeles.localEmbedding (Sum.inr v)) ⊤ :=
      TangentBracket.matrixTangentSpanOver_le_restrictScalars (K := v.adicCompletion F)
        (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)) G (LocalAdeles.localEmbedding (Sum.inr v)) ⊤ hX
    exact TangentBracket.matrixTangentSpan_le_baseChange_infinitesimalStabilizer (K := v.adicCompletion F)
      G hG (LocalAdeles.localEmbedding (Sum.inr v)) ⊤ hm
  · exact finite_infinitesimal_le_prime_tangentSpan G v

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalTangent
