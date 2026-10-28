import OAI.RepresentationTheory.Theta.DerivativeFactorizationDefinitions

/-! # Derivative Factorization Prerequisites -/

namespace OAI.RepresentationTheory.Theta.DerivativeFactorizationPrerequisites

noncomputable section

/-!
Explicit prerequisite propositions copied from the committed CompletedTheta and TensorDecomposition
specifications. No statement theorem or proof placeholder is imported.
DerivativeFactorization itself only needs pure tensor inputs and already assumes the bare
functional equation, so the stronger input propositions are not needed
in the proofs below. They are retained as named conditional inputs.
-/

open scoped Classical _root_.Matrix BoundedContinuousFunction _root_.Matrix.Norms.Elementwise
open _root_.Matrix

namespace Prerequisites
section Definitions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix-coordinate theta sum; a support lattice represents the
restriction of a finite Schwartz–Bruhat input to rational positions. -/
def theta
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (Z : Matrix ι ι ℂ) (z : ι → ℂ) : ℂ :=
  ∑' x : L,
    φ x * Complex.exp
      ((Real.pi : ℂ) * Complex.I *
          AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z (x : ι → ℝ) (x : ι → ℝ) +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (∑ i, (((x : ι → ℝ) i : ℝ) : ℂ) * z i))

/-- `exp ((π/2) zᵀ (Im Z)⁻¹ z) θφ(Z,z)`. -/
def completedTheta
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (Z : Matrix ι ι ℂ) (z : ι → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor
      (((Real.pi : ℂ) / 2) •
        AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z)⁻¹)) z *
    theta L φ Z z

/-- Taylor coefficient, with the `1/a!` normalization. -/
def completedTensor
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (a : ℕ) (Z : Matrix ι ι ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin a => ι → ℂ) ℂ :=
  ((Nat.factorial a : ℂ)⁻¹) •
    iteratedFDeriv ℂ a (completedTheta L φ Z) 0

def siegelDomain : Set (Matrix ι ι ℂ) :=
  {Z | Z.IsSymm ∧ Matrix.PosDef (fun i j => (Z i j).im)}

end Definitions

def Statement : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L Lnew : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [DiscreteTopology Lnew]
    (φ : L →ᵇ ℂ) (φnew : Lnew →ᵇ ℂ)
    (gQ : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℚ)
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    (_hA : g.A = gQ.A.map (algebraMap ℚ ℝ))
    (_hB : g.B = gQ.B.map (algebraMap ℚ ℝ))
    (_hC : g.C = gQ.C.map (algebraMap ℚ ℝ))
    (_hD : g.D = gQ.D.map (algebraMap ℚ ℝ))
    (halfDet : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι → ℂ)
    (_hHalfDet : ∀ Z,
      halfDet Z ^ 2 = (g.complexify.denominator Z.matrix).det)
    (_hPoisson : ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      theta Lnew φnew (g.transformSiegel Z).matrix
          (g.jacobiChange Z z) =
        halfDet Z *
          (Complex.exp (g.thetaCorrectionForm Z z z) *
            theta L φ Z.matrix z)),
    -- Smooth dependence on the period matrix.
    (∀ a : ℕ,
      ContDiffOn ℝ ⊤ (completedTensor L φ a) siegelDomain) ∧
    -- The Taylor tensor is symmetric.
    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
        (σ : Equiv.Perm (Fin a)) (v : Fin a → (ι → ℂ)),
      completedTensor L φ a Z.matrix (fun i => v (σ i)) =
        completedTensor L φ a Z.matrix v) ∧
    -- Covariance of the full completed expression.
    (∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      completedTheta Lnew φnew (g.transformSiegel Z).matrix
          (g.jacobiChange Z z) =
        halfDet Z * completedTheta L φ Z.matrix z) ∧
    -- Covariance in every Taylor degree, including degree zero.
    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
        (v : Fin a → (ι → ℂ)),
      completedTensor Lnew φnew a (g.transformSiegel Z).matrix
          (fun i => g.jacobiChange Z (v i)) =
        halfDet Z * completedTensor L φ a Z.matrix v)

end Prerequisites

namespace Prerequisites.TensorDecomposition

abbrev SchwartzBruhat (X : Type*) [TopologicalSpace X] :=
  { f : X → ℂ // IsLocallyConstant f ∧ HasCompactSupport f }

def ProductStatement : Prop :=
  ∀
    {ι : Type*} [Fintype ι]
    (X : ι → Type*)
    [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)]
    [∀ i, LocallyCompactSpace (X i)]
    [∀ i, TotallyDisconnectedSpace (X i)]
    (φ : SchwartzBruhat ((i : ι) → X i)),
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (ψ : Fin n → (i : ι) → SchwartzBruhat (X i)),
      ∀ x : (i : ι) → X i,
        φ.1 x = ∑ j : Fin n, c j * ∏ i : ι, (ψ j i).1 (x i)

def LocalStatement : Prop :=
  ∀
    {ν : Type*} [DecidableEq ν]
    (V : ν → Type*)
    [∀ v, TopologicalSpace (V v)]
    [∀ v, T2Space (V v)]
    [∀ v, LocallyCompactSpace (V v)]
    [∀ v, TotallyDisconnectedSpace (V v)]
    (K : (v : ν) → Set (V v))
    (_hK_compact : ∀ v, IsCompact (K v))
    (_hK_open : ∀ v, IsOpen (K v))
    (_hK_nonempty : ∀ v, (K v).Nonempty)
    (p : ν)
    (φ : SchwartzBruhat (RestrictedProduct V K Filter.cofinite)),
    ∃ (S : Finset ν) (n : ℕ) (c : Fin n → ℂ)
      (ψ : Fin n → (v : S) → SchwartzBruhat (V v.1)),
      p ∈ S ∧
      ∀ x : RestrictedProduct V K Filter.cofinite,
        φ.1 x =
          if ∀ v, v ∉ S → x v ∈ K v then
            ∑ j : Fin n,
              c j * ∏ v : S, (ψ j v).1 (x v.1)
          else 0

universe u₁ u₂ u₃ u₄

def Statement : Prop := ProductStatement.{u₁, u₂} ∧ LocalStatement.{u₃, u₄}

end Prerequisites.TensorDecomposition

end

end OAI.RepresentationTheory.Theta.DerivativeFactorizationPrerequisites
