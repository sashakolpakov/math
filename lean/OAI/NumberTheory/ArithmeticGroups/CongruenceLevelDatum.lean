import OAI.NumberTheory.ArithmeticGroups.Data

/-! # Congruence Level Datum -/

namespace OAI.NumberTheory.ArithmeticGroups.CongruenceLevelDatum

noncomputable section

/-!
Explicit prerequisite propositions and the unchanged content of CongruenceLevel.
The PrescribedSigns input is its full statement, specialized to E and the place index.
The Riemann input is RiemannProjectivity specialized to the universe of the finite-dimensional
complex tangent spaces used here. Neither definition asserts its own truth.
-/
open scoped Classical

def PrescribedSignsInput (E Place : Type*)
    [Field E] [Algebra ℚ E] [NumberField E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Fintype Place] : Prop :=
  ∀
    (σ : Place → E →ₐ[ℚ] ℂ)
    (_hσ : Function.Bijective
      (fun p : Place × Bool =>
        if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Place)
    (δ : E) (_hδ : δ ≠ 0)
    (_hδc : NumberField.IsCMField.complexConj E δ = -δ)
    (H : Matrix (Fin 3) (Fin 3) E)
    (_hHermitian : ∀ j k,
      H j k = NumberField.IsCMField.complexConj E (H k j))
    -- An adapted basis at μ: the first two coordinates are
    -- positive, and the final basis vector is negative.
    (_hμpos : ∀ x : Geometry.ComplexBall.PrescribedSignsB.Vec, x ≠ 0 → x 2 = 0 →
      0 < (Geometry.ComplexBall.PrescribedSignsB.localB σ H μ x (star x)).re)
    (_hμneg :
      (Geometry.ComplexBall.PrescribedSignsB.localB σ H μ ![0, 0, 1] ![0, 0, 1]).re < 0)
    (_hcompact : ∀ τ, τ ≠ μ →
      (∀ x : Geometry.ComplexBall.PrescribedSignsB.Vec, x ≠ 0 →
        0 < (Geometry.ComplexBall.PrescribedSignsB.localB σ H τ x (star x)).re) ∨
      (∀ x : Geometry.ComplexBall.PrescribedSignsB.Vec, x ≠ 0 →
        (Geometry.ComplexBall.PrescribedSignsB.localB σ H τ x (star x)).re < 0))
    (d : Fin 2 → Place → Bool),
    let B := Geometry.ComplexBall.PrescribedSignsB.localB σ H
    let O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart :=
      {z | (B μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0}
    let r := 3 * Fintype.card Place
    ∃ (a : Fin 2 → E)
      (ℱ : Fin 2 → Geometry.ComplexBall.PrescribedSignsB.BallChart → Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place)),
      let ψ : Fin 2 → Geometry.ComplexBall.PrescribedSignsB.Ambient Place → Geometry.ComplexBall.PrescribedSignsB.Ambient Place → ℂ :=
        fun i => Geometry.ComplexBall.PrescribedSignsB.tracePairing B (fun τ => σ τ (δ * a i))
      -- Wᵢ = E, with hᵢ(s,t) = aᵢ s c(t).
      (∀ i, a i ≠ 0 ∧
        NumberField.IsCMField.complexConj E (a i) = a i ∧
        (σ μ (δ * a i)).im < 0) ∧
      (∀ i, Geometry.ComplexBall.PrescribedSignsB.HolomorphicFamily O r (ℱ i)) ∧
      (∀ i z, z ∈ O →
        (∀ u, u ∈ ℱ i z ↔ Geometry.ComplexBall.PrescribedSignsB.Prescribed B μ (d i) z u) ∧
        Geometry.ComplexBall.PrescribedSignsB.PositivePeriod r (ψ i) Geometry.ComplexBall.PrescribedSignsB.realConj (ℱ i z)) ∧
      -- W = W₁ ⊥ W₂.
      Geometry.ComplexBall.PrescribedSignsB.HolomorphicFamily O (r + r)
        (fun z => (ℱ 0 z).prod (ℱ 1 z)) ∧
      (∀ z, z ∈ O →
        Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (r + r)
          (fun u v => ψ 0 u.1 v.1 + ψ 1 u.2 v.2)
          (fun u => (Geometry.ComplexBall.PrescribedSignsB.realConj u.1, Geometry.ComplexBall.PrescribedSignsB.realConj u.2))
          ((ℱ 0 z).prod (ℱ 1 z))) ∧
      -- Compatibility with the rational trace form.
      (∀ (i : Fin 2) (x y : Fin 3 → E),
        ψ i (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)
          (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y) =
        ((Algebra.trace ℚ E
          (δ * a i *
            (∑ j, ∑ k,
              x j * H j k *
                NumberField.IsCMField.complexConj E (y k)))) : ℂ))

def RiemannInput : Prop :=
  ∀ (T : Type) [NormedAddCommGroup T] [NormedSpace ℂ T] [FiniteDimensional ℂ T]
    (Γ : AddSubgroup T) [DiscreteTopology Γ] [CompactSpace (T ⧸ Γ)],
    Data.CongruenceLevel.IsProjectiveComplexTorus T Γ ↔
      ∃ H : T →ₗ⋆[ℂ] T →ₗ[ℂ] ℂ,
        (∀ u v : T, H v u = star (H u v)) ∧
        (∀ u : T, u ≠ 0 → 0 < (H u u).re) ∧
        (∀ u ∈ Γ, ∀ v ∈ Γ, ∃ m : ℤ, (H u v).im = (m : ℝ))

def ReferenceDatum {E Place : Type*}
    [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ) (μ : Place) (b : E) (dref : Place → Bool) : Prop :=
    let B := Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b])
    let O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart :=
      {z | (B μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0}
    ∃ (δ : E) (m : ℕ)
      (Λ : Submodule ℤ (Data.CongruenceLevel.VE E))
      (ℱ : Geometry.ComplexBall.PrescribedSignsB.BallChart → Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place)),
      δ ≠ 0 ∧
      NumberField.IsCMField.complexConj E δ = -δ ∧
      0 < m ∧
      let ψ : Data.CongruenceLevel.VE E → Data.CongruenceLevel.VE E → ℚ :=
        fun x y =>
          (m : ℚ) *
            Algebra.trace ℚ E (δ * Data.CongruenceLevel.hermitian b x y)
      Data.CongruenceLevel.FullStableLattice Λ ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ,
        ∃ n : ℤ, ψ x y = (n : ℚ)) ∧
      (∀ x, ψ x x = 0) ∧
      (∀ x, (∀ y, ψ x y = 0) → x = 0) ∧
      -- The O_E-action has conjugation as its polarization adjoint.
      (∀ (a : E) (x y : Data.CongruenceLevel.VE E),
        ψ (a • x) y =
          ψ x (NumberField.IsCMField.complexConj E a • y)) ∧
      -- The E-linear isometries are precisely those of V.
      (∀ g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E,
        (∀ x y, ψ (g x) (g y) = ψ x y) ↔
        (∀ x y,
          Data.CongruenceLevel.hermitian b (g x) (g y) =
            Data.CongruenceLevel.hermitian b x y)) ∧
      Geometry.ComplexBall.PrescribedSignsB.HolomorphicFamily O (3 * Fintype.card Place) ℱ ∧
      (∀ z ∈ O,
        (∀ u, u ∈ ℱ z ↔ Geometry.ComplexBall.PrescribedSignsB.Prescribed B μ dref z u) ∧
        Data.CongruenceLevel.AnalyticPolarizedFiber σ Λ ψ (ℱ z)) ∧
      -- Arbitrarily deep principal levels with no finite stabilizers.
      (∀ N₀ : ℕ, 0 < N₀ →
        ∃ N : ℕ, 3 ≤ N ∧ N₀ ∣ N ∧
          ∀ g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E,
            Data.CongruenceLevel.PrincipalLevel b Λ N g →
            ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1)

end

end OAI.NumberTheory.ArithmeticGroups.CongruenceLevelDatum
