import OAI.Analysis.DifferentialForms.Coordinates
import OAI.Analysis.DifferentialForms.WeakApproximation
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientSigns

/-! # Rational Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSplitting.CM

noncomputable section

/-! The arithmetic approximation argument for the original multiplicity
space. This uses the native local splitting and weak approximation proofs;
it has no theta-section or nonvanishing parameters. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open _root_.Module

theorem rational_splitting_approximation
    {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Fintype Place]
    (hWeakApproximation : Analysis.DifferentialForms.WeakApproximation.Local.WeakApproximationInput (E := E) (Place := Place))
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Place) (a : Fin 2 → E)
    (ha_fixed : ∀ i, NumberField.IsCMField.complexConj E (a i) = a i)
    (ha_nonzero : ∀ i, a i ≠ 0)
    (dOld dNew : Fin 2 → Place → Bool)
    (hbalance : ∀ τ, ComplexMultiplication.SignSwitch.CM.signValue (dOld 0 τ) + ComplexMultiplication.SignSwitch.CM.signValue (dOld 1 τ) =
      ComplexMultiplication.SignSwitch.CM.signValue (dNew 0 τ) + ComplexMultiplication.SignSwitch.CM.signValue (dNew 1 τ))
    (η : Place → ℝ)
    (hOldSigns : ∀ i τ, 0 < (ComplexMultiplication.SignSwitch.CM.signValue (dOld i τ) : ℝ) * η τ * (σ τ (a i)).re)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : Basis (Fin 2) E (Analysis.DifferentialForms.Coordinates.LocalApproximation.W E),
      Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0 ∧
      (∀ i, Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i) ≠ 0) ∧
      (∀ y : Analysis.DifferentialForms.Coordinates.LocalApproximation.W E, y ∈ Submodule.span E {b 1} ↔ Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) y = 0) ∧
      (∀ i τ, 0 < (ComplexMultiplication.SignSwitch.CM.signValue (dNew i τ) : ℝ) * η τ *
        (σ τ (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i))).re) ∧
      ∀ τ, dist (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (σ τ) b (fun i => dNew i τ))
        (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (σ τ) (Pi.basisFun E (Fin 2)) (fun i => dOld i τ)) < ε := by
  have hend : ∀ τ : Place, ∃ r : Bool,
      Analysis.DifferentialForms.Coordinates.LocalApproximation.Good (fun i => σ τ (a i)) (η τ) (fun i => dNew i τ)
        (Analysis.DifferentialForms.Coordinates.LocalApproximation.matrixPeriod 1 (fun i => dOld i τ)) ε (if r then 1 else 0) := by
    intro τ
    exact Analysis.DifferentialForms.Coordinates.LocalApproximation.exists_good_endpoint (fun i => σ τ (a i))
      (fun i => (map_ne_zero (σ τ)).mpr (ha_nonzero i))
      (η τ) (fun i => dOld i τ) (fun i => dNew i τ)
      (hbalance τ) (fun i => hOldSigns i τ) ε hε
  choose r hr using hend
  have hnb : ∀ τ : Place, ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ,
      dist z (if r τ then 1 else 0) < δ →
        Analysis.DifferentialForms.Coordinates.LocalApproximation.Good (fun i => σ τ (a i)) (η τ) (fun i => dNew i τ)
          (Analysis.DifferentialForms.Coordinates.LocalApproximation.matrixPeriod 1 (fun i => dOld i τ)) ε z := by
    intro τ
    exact Analysis.DifferentialForms.Coordinates.LocalApproximation.good_neighborhood _ _ _ _ _ _ (hr τ)
  choose δ hδ hgood using hnb
  obtain ⟨t, ht⟩ := Analysis.DifferentialForms.WeakApproximation.Local.approximate_local_field_elements hWeakApproximation σ hσ.injective
    (fun τ => if r τ then (1 : E) else 0) δ hδ
  have hg : ∀ τ : Place,
      Analysis.DifferentialForms.Coordinates.LocalApproximation.Good (fun i => σ τ (a i)) (η τ) (fun i => dNew i τ)
        (Analysis.DifferentialForms.Coordinates.LocalApproximation.matrixPeriod 1 (fun i => dOld i τ)) ε (σ τ t) := by
    intro τ
    apply hgood τ
    by_cases hrt : r τ = true <;> simpa [hrt] using ht τ
  let M := Analysis.DifferentialForms.Coordinates.LocalApproximation.splitMatrix (NumberField.IsCMField.complexConj E).toRingHom a t
  have hM : M.det ≠ 0 := by
    intro hz
    apply (hg μ).1
    rw [← Analysis.DifferentialForms.Coordinates.LocalApproximation.embedding_splitMatrix (σ μ) a t]
    change (M.map (σ μ)).det = 0
    calc
      (M.map (σ μ)).det = σ μ M.det := ((σ μ).map_det M).symm
      _ = 0 := by rw [hz, map_zero]
  let b := Analysis.DifferentialForms.Coordinates.LocalApproximation.basisOfMatrix M hM
  have hb : ∀ τ, Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (σ τ) b =
      Analysis.DifferentialForms.Coordinates.LocalApproximation.localMatrix (fun i => σ τ (a i)) (σ τ t) := by
    intro τ
    exact Analysis.DifferentialForms.Coordinates.LocalApproximation.embedding_basis (σ τ) a t hM
  have hsign : ∀ i τ,
      0 < (ComplexMultiplication.SignSwitch.CM.signValue (dNew i τ) : ℝ) * η τ *
        (σ τ (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i))).re := by
    intro i τ
    rw [Analysis.DifferentialForms.Coordinates.LocalApproximation.embedding_hermitian_self]
    have hv : (fun j => σ τ (b i j)) =
        (fun j => Analysis.DifferentialForms.Coordinates.LocalApproximation.localMatrix (fun k => σ τ (a k)) (σ τ t) j i) := by
      funext j
      exact congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C j i) (hb τ)
    rw [hv]
    exact (hg τ).2.1 i
  have hnondeg : ∀ i, Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b i) (b i) ≠ 0 := by
    intro i hz
    have hp := hsign i μ
    rw [hz, map_zero, Complex.zero_re, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0 :=
    Analysis.DifferentialForms.Coordinates.LocalApproximation.split_basis_orthogonal a ha_fixed t hM
  refine ⟨b, horth, hnondeg, Analysis.DifferentialForms.Coordinates.LocalApproximation.orthocomplement_of_basis a b horth (hnondeg 0),
    hsign, ?_⟩
  intro τ
  change dist
    (Analysis.DifferentialForms.Coordinates.LocalApproximation.matrixPeriod (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (σ τ) b) (fun i => dNew i τ))
    (Analysis.DifferentialForms.Coordinates.LocalApproximation.matrixPeriod (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (σ τ) (Pi.basisFun E (Fin 2)))
      (fun i => dOld i τ)) < ε
  rw [hb, Analysis.DifferentialForms.Coordinates.LocalApproximation.original_basis_matrix]
  exact (hg τ).2.2

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSplitting.CM
