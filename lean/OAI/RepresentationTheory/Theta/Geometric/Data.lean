import OAI.RepresentationTheory.Theta.Geometric.TateComparison
import OAI.RepresentationTheory.Theta.Geometric.Period.Ne
import OAI.RepresentationTheory.Theta.Geometric.Away
import OAI.RepresentationTheory.Theta.Geometric.Differentials
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups

/-! # Data -/

namespace OAI.RepresentationTheory.Theta.Geometric.Data

noncomputable section

/-!
Candidate data for the repaired GeometricTheta statement. The PEL scheme and its
correspondences are TateComparison's native objects. Theta is constructed from PoissonAutomorphy's
actual input space. No Hecke action, branch identification, algebraic theta
lift, or covariance conclusion is a field of this record.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (E K : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] (s q : ℕ) [Fact q.Prime]
  (ι Ga MpR MpF MpA : Type) [Fintype ι] [DecidableEq ι]
  [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]

structure ActiveHeckeThetaData where
  pel : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q
  localEmbedding : Fin s × Bool → E →+* ℚ_[q]
  away : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU pel.reference.b →* Ga
  localLevel : {U : OpenSubgroup (SphericalGU.Spherical.SL3 q) //
    U.toSubgroup = SphericalGU.Spherical.integralSL3 q}
  awayLevel : OpenSubgroup Ga
  weil : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA
  splitting : SphericalGU.Spherical.SL3 q × Ga →* MpF
  period : LinearTheta.BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι
  project : LinearTheta.BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] LinearTheta.Cotangent

namespace ActiveHeckeThetaData

variable {E K s q ι Ga MpR MpF MpA}
  (D : ActiveHeckeThetaData E K s q ι Ga MpR MpF MpA)

abbrev RationalSU := Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.pel.reference.b
abbrev domain := Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b)

def activeLocal : D.RationalSU →* SphericalGU.Spherical.SL3 q :=
  (Matrix.SpecialLinearGroup.map (D.localEmbedding (D.pel.reference.distinguished, false))).comp
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (NumberField.IsCMField.complexConj E).toRingHom
      D.pel.reference.b).subtype

def rationalFinite : D.RationalSU →* SphericalGU.Spherical.SL3 q × Ga :=
  D.activeLocal.prod D.away

def rationalLinear : D.RationalSU →*
    ((Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) :=
  Matrix.SpecialLinearGroup.toLin'.comp
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (NumberField.IsCMField.complexConj E).toRingHom
      D.pel.reference.b).subtype

/-- Invert q in the actual reference lattice. This retains precisely the
lattice conditions away from q; the level below also retains its marking. -/
def awayLattice : Submodule ℤ (Fin 3 → E) :=
  Submodule.span ℤ {v | ∃ n : ℕ, (q : ℤ) ^ n • v ∈ D.pel.reference.lattice}

def rationalAwayLevel : Subgroup D.RationalSU :=
  (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup D.awayLattice.toAddSubgroup D.pel.level).comap D.rationalLinear

def localMatrix (v : Fin s × Bool) : D.RationalSU →* SphericalGU.Spherical.SL3 q :=
  (Matrix.SpecialLinearGroup.map (D.localEmbedding v)).comp
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (NumberField.IsCMField.complexConj E).toRingHom
      D.pel.reference.b).subtype

def localReferenceLattice (v : Fin s × Bool) : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  Submodule.span ℤ_[q]
    ((fun x : Fin 3 → E => fun i => D.localEmbedding v (x i)) ''
      (D.pel.reference.lattice : Set (Fin 3 → E)))

def standardLocalLattice : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  Submodule.span ℤ_[q] (Set.range fun i : Fin 3 => Pi.single i 1)

/-- The local coordinate and the away-level model have their literal
marked-lattice meanings. This contains no branch or Hecke assertion. -/
def HasFiniteCoordinates : Prop :=
  (∀ (v : Fin s × Bool) (a : NumberField.RingOfIntegers E),
    D.localEmbedding v a = D.pel.localCharacter v a) ∧
  (∀ v, D.localReferenceLattice v = standardLocalLattice (q := q)) ∧
  (∀ γ : D.RationalSU, D.away γ ∈ D.awayLevel ↔
    γ ∈ D.rationalAwayLevel ∧ ∀ v : Fin s × Bool,
      v.1 ≠ D.pel.reference.distinguished → D.localMatrix v γ ∈ SphericalGU.Spherical.integralSL3 q)

def finiteWeil : SphericalGU.Spherical.SL3 q × Ga →*
    (PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] PoissonAutomorphyNormalizationData.finiteSchwartz ι) :=
  Descent.finiteWeilFromSplitting D.weil D.splitting

abbrev sphericalInputs :=
  SphericalGU.Spherical.fixedInputs ((SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup) D.finiteWeil

def sphericalWeil (T : SphericalGU.Spherical.SL3Hecke q) :
    D.sphericalInputs →ₗ[ℂ] D.sphericalInputs :=
  Away.Spherical.productWeilAction (SphericalGU.Spherical.integralSL3 q) D.awayLevel.toSubgroup D.finiteWeil T

def sphericalWeilLinear : SphericalGU.Spherical.SL3Hecke q →ₗ[ℚ]
    Module.End ℂ D.sphericalInputs :=
  Away.Spherical.productWeilActionLinear (SphericalGU.Spherical.integralSL3 q)
    D.awayLevel.toSubgroup D.finiteWeil

@[instance_reducible] def periodAction : MulAction D.RationalSU LinearTheta.BallCoordinates :=
  Period.Ne.rationalPeriodAction D.pel.reference.b D.pel.reference.μ

def periodMap (γ : D.RationalSU) : LinearTheta.BallCoordinates → LinearTheta.BallCoordinates :=
  Period.Ne.rationalPeriodPerm D.pel.reference.b D.pel.reference.μ γ

theorem periodMap_preserves (γ : D.RationalSU) (x : LinearTheta.BallCoordinates) (hx : x ∈ D.domain) :
    D.periodMap γ x ∈ D.domain :=
  Period.Ne.rationalPeriodPerm_preserves D.pel.reference.b D.pel.reference.μ γ x hx

theorem periodMap_differentiableAt (γ : D.RationalSU) (x : D.domain) :
    DifferentiableAt ℂ (D.periodMap γ) x.val :=
  (Period.Ne.rationalPeriodPerm_differentiableOn D.pel.reference.b D.pel.reference.μ γ
    x.val x.property).differentiableAt (D.domain.isOpen.mem_nhds x.property)

/-- The theta one-form is the constructed first coefficient and projection. -/
def thetaUniversal : PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] (LinearTheta.BallCoordinates → LinearTheta.Cotangent) :=
  LinearTheta.thetaOneFormLinear D.period D.project

def HasHolomorphicThetaData : Prop :=
  DifferentiableOn ℂ (fun x => (D.period x).matrix) D.domain ∧
    DifferentiableOn ℂ D.project D.domain

/-- Exactly rational automorphy of the canonical ThetaOneForms form, before any
Hecke sum. The period derivative and finite Weil action are constructed. -/
def HasRationalThetaCovariance : Prop :=
  ∀ (γ : D.RationalSU) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : D.domain),
    (D.thetaUniversal (D.finiteWeil (D.rationalFinite γ) φ)
      (D.periodMap γ x.val)).comp (fderiv ℂ (D.periodMap γ) x.val) =
        D.thetaUniversal φ x.val

end ActiveHeckeThetaData

end

end OAI.RepresentationTheory.Theta.Geometric.Data
