import OAI.Geometry.ComplexBall.ArithmeticQuotient
import OAI.Geometry.ComplexBall.Cone

/-! # Arithmetic Quotient Conditional -/

namespace OAI.Geometry.ComplexBall.ArithmeticQuotientConditional

noncomputable section

/-! ArithmeticQuotient conditional on the committed WeakApproximation, Lattices and TorsionFreeLevel specifications.
The coefficient, algebraic realization, arithmetic presentation, ball action,
quotient atlas and natural projection are all constructed in the helper files. -/

open scoped Classical _root_.Manifold
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.NumberField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

theorem existence_of_compact_ball_quotients_conditional
    (hWeakApproximation : Fields.ArithmeticQuotient.WeakApproximationInput E)
    (hLattices : ∀ (k : Type) [Field k] [NumberField k], ArithmeticQuotient.ArithmeticLatticeInput k)
    (hTorsionFreeLevel : Levels.ArithmeticQuotient.TorsionFreeLevelsInput E)
    [IsGalois ℚ E]
    (μ : E →+* ℂ)
    -- There is a real place other than the one underlying μ.
    (h_other_place :
      ∃ ν : E →+* ℂ,
        ν ≠ μ ∧ ν ≠ (starRingEnd ℂ).comp μ) :
    ∃ b : E,
      NumberField.IsCMField.complexConj E b = b ∧
      b ≠ 0 ∧
      -- Signature (2,1) at μ and (3,0) at every other real place.
      (μ b).re < 0 ∧
      (∀ ν : E →+* ℂ,
        ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ →
          0 < (ν b).re) ∧
      -- Nondegeneracy and Hermitian anisotropy over E.
      (∀ x : ArithmeticQuotientEquationsData.Vec E,
        (∀ y : ArithmeticQuotientEquationsData.Vec E, ArithmeticQuotientEquationsData.hermitian b x y = 0) → x = 0) ∧
      (∀ x : ArithmeticQuotientEquationsData.Vec E, ArithmeticQuotientEquationsData.hermitian b x x = 0 → x = 0) ∧
      -- Every initial integer principal level has a suitable refinement.
      (∀ N₀ : ℕ, 0 < N₀ →
        ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
          (∀ g : ArithmeticQuotientEquationsData.Mat E, ArithmeticQuotientEquationsData.principalLevel b N g →
            ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
          ∃ R : Setoid (ArithmeticQuotientEquationsData.NegativeVectors b μ),
            (∀ z w, R.r z w ↔ ArithmeticQuotientEquationsData.orbitRelation b μ N z w) ∧
            CompactSpace (Quotient R) ∧
            T2Space (Quotient R) ∧
            SecondCountableTopology (Quotient R) ∧
            ConnectedSpace (Quotient R) ∧
            ∃ atlas : ChartedSpace (Fin 2 → ℂ) (Quotient R),
              letI := atlas
              IsManifold 𝓘(ℂ, Fin 2 → ℂ) 1 (Quotient R) ∧
              -- The natural projection is a holomorphic submersion.
              ∀ z : ArithmeticQuotientEquationsData.NegativeVectors b μ,
                MDifferentiableAt
                  𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, Fin 2 → ℂ)
                  (ArithmeticQuotientEquationsData.projection b μ R z) z.val ∧
                Function.Surjective
                  (mfderiv
                    𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, Fin 2 → ℂ)
                    (ArithmeticQuotientEquationsData.projection b μ R z) z.val)) := by
  obtain ⟨b, hb, hb0, hbμ, hpos, hnd, han⟩ := Fields.ArithmeticQuotient.exists_anisotropic_signature hWeakApproximation μ h_other_place
  refine ⟨b, hb, hb0, hbμ, hpos, hnd, han, ?_⟩
  intro N₀ hN₀
  obtain ⟨N, hN, hdiv, ht⟩ := Levels.ArithmeticQuotient.matrix_levels_torsion_free hTorsionFreeLevel b N₀ hN₀
  let Γ := (Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ)
  have ha := ArithmeticQuotient.principalUnitary_lattice_compact_universe hLattices b hb hb0 μ hpos h_other_place N hN
  let : DiscreteTopology Γ := ha.1.1
  let : CompactSpace (ArithmeticQuotientEquationsData.ArchimedeanSU b μ ⧸ Γ) := ha.2
  have hbim : (μ b).im = 0 := by
    have he := congrArg μ hb
    rw [IsCMField.complexEmbedding_complexConj] at he
    exact Complex.conj_eq_iff_im.mp he
  let : ProperlyDiscontinuousSMul Γ (ArithmeticQuotientBoostBall.Ball (μ b)) :=
    ArithmeticQuotientBoostBall.discrete_ballAction_properlyDiscontinuous (μ b) hbim hbμ Γ
  let : IsCancelSMul Γ (ArithmeticQuotientBoostBall.Ball (μ b)) := Free.ArithmeticQuotient.free_of_properlyDiscontinuous_torsionFree
    (Free.ArithmeticQuotient.principalImage_torsionFree b N μ ht)
  have htop := Cone.ArithmeticQuotient.coneQuotient_topological_properties (μ b) hbim hbμ Γ
  refine ⟨N, hN, hdiv, ht, Free.ArithmeticQuotient.coneOrbitSetoid (μ b) Γ, ?_, htop.1, htop.2.1,
    htop.2.2.1, htop.2.2.2, Cone.ArithmeticQuotient.coneQuotientAtlas (μ b) hbμ Γ, ?_, ?_⟩
  · exact Free.ArithmeticQuotient.coneOrbitSetoid_principal_iff b μ N
  · exact Cone.ArithmeticQuotient.coneQuotientAtlas_isManifold (μ b) hbμ Γ
  · intro z
    exact Cone.ArithmeticQuotient.coneQuotient_projection_submersion (μ b) hbμ Γ z

end

end OAI.Geometry.ComplexBall.ArithmeticQuotientConditional
