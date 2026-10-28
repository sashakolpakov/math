import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallRealization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallOrbitQuotient
import Mathlib.Topology.Homeomorph.Quotient

/-! # Orbit Realization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The literal principal orbit quotient is homeomorphic to the
arithmetic matrix-group ball quotient, with the original projections
identified exactly. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (N : ℕ)

def Datum.RankThreePELDatum.principalArchimedeanEquiv : Groups.principalSpecialUnitary P.b P.lattice N ≃* P.principalArchimedeanSubgroup N :=
  MonoidHom.ofInjective (P.principalArchimedeanMap_injective N)

theorem Datum.RankThreePELDatum.principalArchimedeanEquiv_action (g : Groups.principalSpecialUnitary P.b P.lattice N) (z : P.Domain) :
    P.arithmeticBallEquiv (g • z) = P.principalArchimedeanEquiv N g • P.arithmeticBallEquiv z :=
  P.arithmeticBallEquiv_action N g z

theorem Datum.RankThreePELDatum.principalOrbit_arithmetic_iff (z w : P.Domain) :
    (P.principalOrbitSetoid N).r z w ↔
      MulAction.orbitRel (P.principalArchimedeanSubgroup N) (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b))
        (P.arithmeticBallEquiv z) (P.arithmeticBallEquiv w) := by
  change (∃ g : Groups.principalSpecialUnitary P.b P.lattice N, g • w = z) ↔
    ∃ g : P.principalArchimedeanSubgroup N, g • P.arithmeticBallEquiv w = P.arithmeticBallEquiv z
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨P.principalArchimedeanEquiv N g,
      (P.principalArchimedeanEquiv_action N g w).symm.trans (congrArg P.arithmeticBallEquiv hg)⟩
  · rintro ⟨g, hg⟩
    obtain ⟨g, rfl⟩ := (P.principalArchimedeanEquiv N).surjective g
    exact ⟨g, P.arithmeticBallEquiv.injective ((P.principalArchimedeanEquiv_action N g w).trans hg)⟩

def Datum.RankThreePELDatum.principalOrbitHomeomorph : Quotient (P.principalOrbitSetoid N) ≃ₜ
    MulAction.orbitRel.Quotient (P.principalArchimedeanSubgroup N) (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b)) :=
  Homeomorph.Quotient.congr P.arithmeticBallEquiv (P.principalOrbit_arithmetic_iff N)

theorem Datum.RankThreePELDatum.principalOrbitHomeomorph_projection (z : P.Domain) :
    P.principalOrbitHomeomorph N (P.principalOrbitProjection N z) =
      Quotient.mk (MulAction.orbitRel (P.principalArchimedeanSubgroup N) (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b)))
        (P.arithmeticBallEquiv z) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
