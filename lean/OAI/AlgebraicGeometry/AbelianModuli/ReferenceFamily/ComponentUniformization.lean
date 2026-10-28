import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyRealization
import Mathlib.Topology.Covering.Basic

/-! # Component Uniformization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Component geometry and uniformization have their actual scheme and
complex-manifold meanings. None of these predicates is an input field
of the PEL datum or of the candidate moduli model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ}

section

variable (P : Datum.RankThreePELDatum E s)

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.domain_isOpen : IsOpen P.domain := by
  apply isOpen_lt _ continuous_const
  unfold Geometry.ComplexBall.PrescribedSignsB.localB Geometry.ComplexBall.PrescribedSignsB.lineVector
  fun_prop

def Datum.RankThreePELDatum.domainOpen : TopologicalSpace.Opens Geometry.ComplexBall.PrescribedSignsB.BallChart := ⟨P.domain, P.domain_isOpen⟩

abbrev Datum.RankThreePELDatum.Domain := P.domainOpen

/-- Projective action in the negative-line chart. Its denominator is
nonzero on the domain for the unitary elements used in the theorem. -/
def Datum.RankThreePELDatum.lineAction (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : Geometry.ComplexBall.PrescribedSignsB.BallChart :=
  let w := ((LinearMap.toMatrix' g.toLinearMap).map P.μ).mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector z)
  fun i : Fin 2 => w i.castSucc / w 2

def Datum.RankThreePELDatum.OrbitRelation (Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (z w : P.Domain) : Prop :=
  ∃ g ∈ Γ, w.val = P.lineAction g z.val

/-- A surjective holomorphic covering with invertible complex derivative.
The source carries the standard open-ball complex structure and the target
the proved regular-coordinate atlas of the actual projective variety. -/
def Datum.RankThreePELDatum.IsBallCover (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (q : P.Domain → X.analyticSpace) : Prop :=
  Function.Surjective q ∧ IsCoveringMap q ∧
  MDifferentiable 𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart) 𝓘(ℂ, X.analyticModel) q ∧
  ∀ z, Function.Bijective (mfderiv 𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart) 𝓘(ℂ, X.analyticModel) q z)

/-- The fibers are exactly the orbits of the specified arithmetic group.
This replaces the draft's opaque marked-lattice quotient predicate. -/
def Datum.RankThreePELDatum.IsUniformizedBy (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) : Prop :=
  ∃ q : P.Domain → X.analyticSpace,
    P.IsBallCover X q ∧ ∀ z w, q z = q w ↔ P.OrbitRelation Γ z w

def Datum.RankThreePELDatum.matrixHermitian (H : Matrix (Fin 3) (Fin 3) E) (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : E :=
  ∑ i, ∑ j, x i * H i j * NumberField.IsCMField.complexConj E (y j)

def Datum.RankThreePELDatum.complexMatrixHermitian (τ : E →+* ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (x y : Fin 3 → ℂ) : ℂ :=
  ∑ i, ∑ j, x i * τ (H i j) * star (y j)

def Datum.RankThreePELDatum.lineActionVia (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : Geometry.ComplexBall.PrescribedSignsB.BallChart :=
  let w := e.symm (((LinearMap.toMatrix' g.toLinearMap).map P.μ).mulVec (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)))
  fun i : Fin 2 => w i.castSucc / w 2

/-- All components use genuine rank-three E-Hermitian lattices; the
normalizer transports their distinguished-place domains to P's ball.
This allows different rational Hermitian forms on different components. -/
def Datum.RankThreePELDatum.IsArithmeticBallUniformized (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ) : Prop :=
  ∃ (H : Matrix (Fin 3) (Fin 3) E) (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)),
    (∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i)) ∧
    H.det ≠ 0 ∧ NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ ∧
    (∀ x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0) ∧
    (∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y) ∧
    (∀ i, i ≠ P.distinguished →
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        0 < (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom H x x).re < 0)) ∧
    ∃ q : P.Domain → X.analyticSpace,
      P.IsBallCover X q ∧
      ∀ z w, q z = q w ↔
        ∃ g ∈ (Groups.principalLatticeSubgroup Λ.toAddSubgroup N ⊓
          Groups.specialUnitarySubgroup (Datum.RankThreePELDatum.matrixHermitian H)),
          w.val = P.lineActionVia e g z.val

omit [NumberField E] [NumberField.IsCMField E] in
/-- The explicit covering-and-orbit formulation really identifies the
component with the topological orbit quotient. -/
theorem Datum.RankThreePELDatum.quotient_homeomorph_of_uniformizedBy (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (h : P.IsUniformizedBy X Γ) :
    ∃ R : Setoid P.Domain,
      (∀ z w, R.r z w ↔ P.OrbitRelation Γ z w) ∧
      Nonempty (Quotient R ≃ₜ X.analyticSpace) := by
  obtain ⟨q, hq, horbits⟩ := h
  let qc : C(P.Domain, X.analyticSpace) := ⟨q, hq.2.1.continuous⟩
  have hquot : Topology.IsQuotientMap qc := hq.2.1.isQuotientMap hq.1
  exact ⟨Setoid.ker q, horbits, ⟨hquot.homeomorph⟩⟩

end

variable {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : Models.FinePELModel P iota N) (κ : K →+* ℂ)

/-- An actual smooth projective component, including its scheme inclusion
and the identification with the analytic connected component. -/
def Models.FinePELModel.IsProjectiveComponent (C : M.ComplexComponent κ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Prop :=
  X.complexDimension = 2 ∧
  ∃ f : X.toOver ⟶ M.complexFiber κ,
    IsOpenImmersion f.left ∧ IsClosedImmersion f.left ∧
    Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) =
      {x : M.ComplexPoints κ | ConnectedComponents.mk x = C}

omit [NumberField K] in
/-- Projectivity of the component's actual scheme gives compactness
for the genuine analytic connected component. -/
theorem Models.FinePELModel.component_compact_of_projective (C : M.ComplexComponent κ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (h : M.IsProjectiveComponent κ C X) :
    CompactSpace (M.ComponentPoints κ C) := by
  obtain ⟨_, f, _, hf, hrange⟩ := h
  let : IsClosedImmersion f.left := hf
  have he := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f
  let e : X.analyticSpace ≃ₜ M.ComponentPoints κ C :=
    he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  exact e.compactSpace

def Models.FinePELModel.HasProjectiveBallComponents : Prop :=
  ∀ C : M.ComplexComponent κ,
    ∃ X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety,
      M.IsProjectiveComponent κ C X ∧
      P.IsArithmeticBallUniformized X N

/-- The prescribed marked lattice determines the principal SU group
appearing in the orbit relation, without an abstract comparison field. -/
def Models.FinePELModel.HasPrincipalComponent : Prop :=
  ∃ (C : M.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
    M.IsProjectiveComponent κ C X ∧
    P.IsUniformizedBy X (Groups.principalSpecialUnitary P.b P.lattice N)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
