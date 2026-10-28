import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
import OAI.RepresentationTheory.Theta.Adelic.ConstructSplitPolarization
import OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection

/-! # Data -/

namespace OAI.RepresentationTheory.Theta.Adelic.Data

noncomputable section

/-! Full concrete AdelicTheta proposition. These are definitions of the required
conclusions, with no proof holes and no assumed geometric/Weil/theta
compatibility. The final statement theorem in Statements/AdelicTheta.lean is
proved from the designated prerequisite propositions. -/

open scoped _root_.NumberField Classical _root_.Topology

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection

local instance (F : Type) [Field F] [NumberField F] (v : FiniteSchwartz.FinitePlace F) :
    MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := borel _
local instance (F : Type) [Field F] [NumberField F] (v : FiniteSchwartz.FinitePlace F) :
    BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := ⟨rfl⟩

section Conclusions
variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

/-- Closed idele-class embedding, character extension, and the actual
global quadratic norm character. The splitting characters restrict to
its dimension powers, both globally here and locally in GlobalCharacters. -/
def CharacterConclusion : Prop :=
  Topology.IsClosedEmbedding (IdeleClassInjection.scalarIdeleClass F d) ∧
  (∀ χ : NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass F →ₜ* Circle,
    ∃ χE : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle,
      (∀ a : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ, χE (IdeleClassInjection.quadraticPrincipal F d a) = 1) ∧
      ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ,
        χE (IdeleClassInjection.scalarIdele F d a) = χ (QuotientGroup.mk' (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range a)) ∧
  ∃ ω : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ →ₜ* Circle,
    (∀ a : Fˣ, ω (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F a) = 1) ∧
    (∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ,
      ω a = ∏ᶠ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F, Weil.AdelicSplitting.Characters.Construction.normCharacter F d v (Units.map (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate F v).toMonoidHom a)) ∧
    (∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ, C.χV (IdeleClassInjection.scalarIdele F d a) = ω a ^ n) ∧
    (∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ, C.χW (IdeleClassInjection.scalarIdele F d a) = ω a ^ m)

/-- The corrected AdelicSplitting conclusion in full: adelic covering, local
factorization, and equality with the independently defined rational graph. -/
def AdelicConclusion : Prop :=
  (∀ g : Weil.AdelicSplitting.Integral.Construction.AdelicDualPair F H.val K.val,
    Weil.AdelicSplitting.Vacuum.Construction.globalProjection F (n * m) C.ψ (Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hd C P D g) =
      Weil.AdelicSplitting.Assembly.Construction.adelicDualPairAction F d n m H K hd C P D g) ∧
  (∀ v (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val v × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val v),
    Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Weil.AdelicSplitting.Integral.Construction.includeUnitaryPlace F H.val K.val v g) =
      Weil.AdelicSplitting.Vacuum.Construction.globalInclude F (n * m) C.ψ v (D.atPlace v g)) ∧
  (∃ r : Weil.Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) →* Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F (n * m) C.ψ,
    (∀ γ a, (γ, a) ∈ Weil.AdelicSplitting.Rational.Construction.rationalGraph F (n * m) C.ψ ↔ r γ = a) ∧
    (∀ γ, Weil.AdelicSplitting.Vacuum.Construction.globalProjection F (n * m) C.ψ (r γ) = Weil.AdelicSplitting.Vacuum.Construction.rationalSymplectic F (n * m) γ) ∧
    (∀ g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val,
      Weil.AdelicSplitting.Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Weil.AdelicSplitting.Integral.Construction.rationalPair F H.val K.val g) =
        r (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g)))

/-- Smoothness and cofinal compact open stabilizers for the concrete
restricted tensor product of finite Schwartz-Bruhat functions. -/
def FiniteConclusion : Prop :=
  (∀ f : FiniteSchwartz.finiteSchwartz F (n * m),
    IsOpen {g : FiniteSchwartz.FiniteSU F H | FiniteSchwartz.finiteAction F H K hd C P D g f = f}) ∧
  (∀ (Φ : Finset (FiniteSchwartz.finiteSchwartz F (n * m))) (K₀ : OpenSubgroup (FiniteSchwartz.FiniteSU F H)),
    ∃ L : OpenSubgroup (FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
      ∀ f ∈ Φ, ∀ g ∈ L, FiniteSchwartz.finiteAction F H K hd C P D g f = f)

end Conclusions

/-- All-dimensional local/global unitary dual-pair splitting. The
characters and normalized local splittings are existential conclusions. -/
def GeneralSplittingStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d : F) (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (n m : ℕ), 0 < n * m →
    ∀ (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
      (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ),
      H.val.conjTranspose = H.val → K.val.conjTranspose = -K.val →
      ∀ (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
        (∃ x, ψ x ≠ 1) → (∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1) →
        ∀ P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K,
          ∃ C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m, C.ψ = ψ ∧ CharacterConclusion F d n m C ∧
            ∃ D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hq.1 C P,
              AdelicConclusion F d n m H K hq.1 C P D ∧
              FiniteConclusion F d n m H K hq.1 C P D

/-- At every split finite place, the quadratic root constructs stable
standard/dual coordinates and an oscillator change of polarization. For
one multiplicity line the resulting SL3 action is literal substitution. -/
def SplitMultiplicityOneStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
    (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd C P)
    (v : FiniteSchwartz.FinitePlace F) (r : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))
    (hr : r ^ 2 = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d),
    let B := ConstructSplitPolarization.constructedSplitPolarization F d hd H K hH hK P v r hr
    (∃ w : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F 3 C.ψ (.inr v), Weil.AdelicSplitting.Vacuum.Construction.projectionAt F 3 C.ψ (.inr v) w = B.change ∧
      ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)))
        (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3),
        (Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) 3 (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
          (w * FiniteSchwartz.localSUSplitting F H K hd C P D (.inr v) (B.identify g) * w⁻¹) f).val x =
            f.val ((g⁻¹).val.mulVec x)) ∧
    (∀ χ : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) →* Circle, ∀ g, χ g = 1)

/-- Full geometric specialization used in the manuscript. The only extra
input specifies CM signatures, bases, and the standard additive-character
convention. Periods, geometric identifications, oscillator comparisons,
theta covariance, and genuine congruence descent are all conclusions. -/
def BallCompletedThetaStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d : F) (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (m : ℕ), (m = 1 ∨ m = 2) →
    ∀ (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
      (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ),
      H.val.conjTranspose = H.val → K.val.conjTranspose = -K.val →
      ∀ (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
        (∃ x, ψ x ≠ 1) → (∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1) →
        ∀ (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) (A : BallGeometryData.BallArithmeticData F d m H K),
          DataTheta.Descent.StandardArchCharacter (A := A) ψ →
          ∃ C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m, C.ψ = ψ ∧ CharacterConclusion F d 3 m C ∧
            ∃ D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hq.1 C P,
              AdelicConclusion F d 3 m H K hq.1 C P D ∧
              FiniteConclusion F d 3 m H K hq.1 C P D ∧
              ∃ B : DataTheta.ComparisonData F H K A,
                DataTheta.CoordinateIdentification B P ∧ DataTheta.GeometryIdentification B ∧
                DataTheta.OscillatorIdentification B P hq.1 C D ∧
                SiegelBranchData.SiegelBranchExtension B P hq.1 C D ∧
                SiegelBranchData.ArchimedeanLiftUniqueness P hq.1 C D ∧ DataTheta.Descent.ThetaConstruction B ∧
                DataTheta.Descent.RationalHeckeCovariance B P hq.1 C D ∧ DataTheta.Descent.CongruenceDescent B P hq.1 C D

/-- Complete repaired AdelicTheta, with all the original mathematical clauses. -/
def CompleteStatement : Prop :=
  GeneralSplittingStatement ∧ SplitMultiplicityOneStatement ∧ BallCompletedThetaStatement

end

end OAI.RepresentationTheory.Theta.Adelic.Data
