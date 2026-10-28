import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairDecomposition
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.RealCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ConstructedCover

/-! # Constructed Adelic Group -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM

noncomputable section

/-! The actual adelic metaplectic group and its action, instantiated
from the proved real and finite covers. Unitarity and Heisenberg
covariance of the adelic action are checked separately. -/

open scoped Classical

abbrev RealGroup (n : ℕ) := Real.SchrodingerAction.CM.RealMp n
abbrev FiniteGroup (n : ℕ) := Finite.BareNe.CM.Group.BareGroup (I := Fin n)

abbrev AdelicGroup (n : ℕ) := Adelic.AdelicPairGroup.CM.PairGroup
  (RealCover.CM.realCover n) (Finite.ConstructedCover.CM.finiteCover (Fin n))

def projection (n : ℕ) : AdelicGroup n →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ :=
  Adelic.AdelicPairGroup.CM.projection (RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))

def action (n : ℕ) : AdelicGroup n →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) :=
  Adelic.AdelicPairGroup.CM.action (RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))

def includeReal (n : ℕ) : RealGroup n →* AdelicGroup n :=
  Adelic.AdelicPairGroup.CM.includeReal (RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))

def includeFinite (n : ℕ) : FiniteGroup n →* AdelicGroup n :=
  Adelic.AdelicPairGroup.CM.includeFinite (RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))

def negOne (n : ℕ) : AdelicGroup n :=
  Adelic.PairDecomposition.CM.Kernel.negOne (RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))

theorem projection_surjective (n : ℕ) : Function.Surjective (projection n) :=
  Adelic.AdelicPairGroup.CM.projection_surjective _ _

theorem kernel (n : ℕ) (a : AdelicGroup n) : projection n a = 1 ↔ a = 1 ∨ a = CM.negOne n :=
  Adelic.PairDecomposition.CM.Kernel.kernel _ _ a

theorem negOne_ne_one (n : ℕ) : CM.negOne n ≠ 1 := Adelic.PairDecomposition.CM.Kernel.negOne_ne_one _ _

theorem genuine (n : ℕ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) : action n (CM.negOne n) f = -f := by
  have h := Adelic.PairDecomposition.CM.Kernel.action_negOne (RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))
  exact congrArg (fun U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) => U f) h

theorem faithful (n : ℕ) : Function.Injective (fun a : AdelicGroup n => (projection n a, action n a)) :=
  Adelic.AdelicPairGroup.CM.faithful _ _

theorem commute (n : ℕ) (r : RealGroup n) (f : FiniteGroup n) :
    Commute (includeReal n r) (includeFinite n f) := Adelic.AdelicPairGroup.CM.includes_commute _ _ r f

theorem centralProduct_kernel (n : ℕ) (r : RealGroup n) (f : FiniteGroup n) :
    includeReal n r * includeFinite n f = 1 ↔
      (r = 1 ∧ f = 1) ∨
      (r = (RealCover.CM.realCover n).negOne ∧
        f = (Finite.ConstructedCover.CM.finiteCover (Fin n)).negOne) :=
  Adelic.PairDecomposition.CM.Kernel.centralProduct_kernel _ _ r f

theorem decompose (n : ℕ) (a : AdelicGroup n) (r : RealGroup n)
    (ha : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (projection n a) = (RealCover.CM.realCover n).project r) :
    ∃ f : FiniteGroup n, includeReal n r * includeFinite n f = a :=
  Adelic.PairDecomposition.CM.decompose _ _ a r ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
