import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativePresentation

/-! # Negative Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution

noncomputable section

/-! Actual coherent sheaves on projective space admit augmented resolutions
by finite sums of negative twists above any prescribed bound. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

structure State where
  module : (Proj (homogeneousSubmodule σ R)).Modules
  quasicoherent : module.IsQuasicoherent
  finiteType : module.IsFiniteType

attribute [instance] State.quasicoherent State.finiteType

structure Presentation (M : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) (B : ℕ) where
  count : ℕ
  degree : Fin count → ℕ
  degree_bound : ∀ i, B ≤ degree i
  projection : (∐ fun i : Fin count => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (degree i)) ⟶ M
  epi : Epi projection

attribute [instance] Presentation.epi

namespace Presentation

variable {M : (Proj (homogeneousSubmodule σ R)).Modules} {j : σ} {B : ℕ} (Q : Presentation M j B)

abbrev source := ∐ fun i : Fin Q.count => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (Q.degree i)

instance : Q.source.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j Q.degree

instance : Q.source.IsFiniteType := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType j Q.degree

end Presentation

def presentation (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B : ℕ) :
    Presentation M j B := Classical.choice <| by
  obtain ⟨r, d, f, hd, hf⟩ := AlgebraicGeometry.SheafCohomology.Projective.BoundedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient_above M j B
  exact ⟨⟨r, d, hd, f, hf⟩⟩

local instance : LocallyOfFiniteType (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
  AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType

local instance : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
  LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))

def next (j : σ) (B : ℕ) (s : State (R := R) (σ := σ)) : State (R := R) (σ := σ) where
  module := kernel (presentation s.module j B).projection
  quasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel (presentation s.module j B).projection
  finiteType := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_kernel (presentation s.module j B).projection

def state (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B : ℕ) :
    ℕ → State (R := R) (σ := σ)
  | 0 => ⟨M, inferInstance, inferInstance⟩
  | n + 1 => next j B (state M j B n)

def tower (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B : ℕ) :
    KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules) where
  object n := (NegativeResolution.state M j B n).module
  term n := (presentation (NegativeResolution.state M j B n).module j B).source
  projection n := (presentation (NegativeResolution.state M j B n).module j B).projection
  epi n := (presentation (NegativeResolution.state M j B n).module j B).epi
  kernelIso _n := Iso.refl _

abbrev complex (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B : ℕ) :=
  (tower M j B).complex

def augmentation (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B : ℕ) :
    NegativeResolution.complex M j B ⟶ (ChainComplex.single₀ (Proj (homogeneousSubmodule σ R)).Modules).obj M :=
  (tower M j B).augmentation

instance (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B : ℕ) :
    QuasiIso (NegativeResolution.augmentation M j B) :=
  inferInstanceAs (QuasiIso (tower M j B).augmentation)

def termIso (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B n : ℕ) :
    (NegativeResolution.complex M j B).X n ≅
      ∐ fun i : Fin (presentation (NegativeResolution.state M j B n).module j B).count =>
        AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j
          ((presentation (NegativeResolution.state M j B n).module j B).degree i) := Iso.refl _

theorem degree_bound (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B n : ℕ)
    (i : Fin (presentation (NegativeResolution.state M j B n).module j B).count) :
    B ≤ (presentation (NegativeResolution.state M j B n).module j B).degree i :=
  (presentation (NegativeResolution.state M j B n).module j B).degree_bound i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution
