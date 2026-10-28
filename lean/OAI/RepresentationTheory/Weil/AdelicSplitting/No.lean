import Mathlib
import OAI.RepresentationTheory.Weil.AdelicSplitting.Construction
import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.CentralProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.CompatibilityReduction
import OAI.RepresentationTheory.Weil.AdelicSplitting.ZeroRankCompatibility
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner
import OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFourierCovers
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierRelations
import OAI.RepresentationTheory.Weil.AdelicSplitting.GlobalKernel
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness
import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient
import OAI.RepresentationTheory.Weil.AdelicSplitting.Annihilator
import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidLatticePoisson
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteTestSupport
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanRapid
import OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveTestFamily
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaQuadratic
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
import OAI.RepresentationTheory.Weil.AdelicSplitting.TestFamilyAction
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalCompatibility

/-! # No -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.No

noncomputable section

/-!
# AdelicSplitting: adelic unitary splitting compatible with rational points

The full accepted conclusion is proved below, independently of the statement
module. The local input is the authorized corrected weak normalization.
The historical strong normalization and its AdelicTheta counterexamples remain intact.

Actual adelic Poisson summation makes the prescribed rational Schrödinger
operators preserve theta up to positive scalars. The circle kernel then proves
that their generated subgroup is the graph of a rational homomorphism. Weighted
Fourier-quadratic relations prove Gaussian reciprocity, giving product one for
the corrected unitary normalization factors. Weyl coefficients on doubled
position space convert the weak Cayley formula into a rational quadratic,
Fourier, and linear operator word. Their rational theta identity proves that
the normalized unitary operators also preserve the positive theta ray. Equal
projections and the scalar-kernel theorem identify these operators on the two
open cells; rational unitary factorization extends the comparison to every
rational point. The separately proved zero-rank argument completes all ranks.

No target statement is imported here.

## Historical countermodel for the original uninterpreted interface

The countermodel below concerns the original specification, not a disproof of the
classical adelic unitary splitting theorem. No statement module is imported.

The original specification at b20be31's `IsStandardUnitaryDatum` is an uninterpreted predicate:
its signature permits the interpretation `True`. The comments about actual
unitary groups and compatible Kudla normalizations are not encoded as laws.
Below, even local covering, injective embeddings, and a rational symplectic
section do not imply that the prescribed local and rational sections agree.
All maps are continuous in this example. The obstruction is explicit:
local factorization forces S(-1) = (-1, 1), while rational compatibility
forces S(-1) = (-1, -1).

The original statement also failed elaboration because the scoped notation
`𝓞` was not opened. This countermodel is retained after the specification repair.
-/

open scoped _root_.NumberField

namespace Specification

variable
    {CF CE UQ SpQ UA SpA MpA : Type*}
    [CommGroup CF] [CommGroup CE]
    [Group UQ] [Group SpQ] [Group UA]
    [Group SpA] [Group MpA]
    [TopologicalSpace CF] [TopologicalSpace CE]
    [TopologicalSpace UA] [TopologicalSpace MpA]
    {Place : Type*} {Uv Mpv : Place → Type*}
    [∀ v, Group (Uv v)] [∀ v, Group (Mpv v)]
    [∀ v, TopologicalSpace (Uv v)]
    [∀ v, TopologicalSpace (Mpv v)]

/-- Same fields and types as in the original specification. -/
structure AdelicUnitaryModel where
  classEmbedding : CF →ₜ* CE
  quadraticCharacter : CF →ₜ* Circle
  projection : MpA →* SpA
  dualPairAction : UA →* SpA
  includeU : ∀ v, Uv v →* UA
  includeMp : ∀ v, Mpv v →* MpA
  rationalU : UQ →* UA
  rationalDualPairAction : UQ →* SpQ
  rationalSymplecticSplitting : SpQ →* MpA

abbrev CircleModel := AdelicUnitaryModel
  (CF := PUnit.{1}) (CE := PUnit.{1}) (UQ := Circle) (SpQ := Circle)
  (UA := Circle) (SpA := Circle) (MpA := Circle × Circle)
  (Uv := fun _ : Unit => Circle) (Mpv := fun _ : Unit => Circle × Circle)

def counterexampleModel : CircleModel where
  classEmbedding := ContinuousMonoidHom.id PUnit.{1}
  quadraticCharacter := 1
  projection := MonoidHom.fst Circle Circle
  dualPairAction := MonoidHom.id Circle
  includeU := fun _ => MonoidHom.id Circle
  includeMp := fun _ => MonoidHom.id (Circle × Circle)
  rationalU := MonoidHom.id Circle
  rationalDualPairAction := MonoidHom.id Circle
  rationalSymplecticSplitting :=
    (MonoidHom.id Circle).prod (MonoidHom.id Circle)

def counterexampleLocal : ∀ _ : Unit, Circle →ₜ* Circle × Circle :=
  fun _ => (ContinuousMonoidHom.id Circle).prod 1

/-- The full conclusion in AdelicSplitting, with its specified maps. -/
def HasRequiredSplitting (D : CircleModel)
    (s : ∀ _ : Unit, Circle →ₜ* Circle × Circle) : Prop :=
  ∃ S : Circle →ₜ* Circle × Circle,
    (∀ u, D.projection (S u) = D.dualPairAction u) ∧
    (∀ v u, S (D.includeU v u) = D.includeMp v (s v u)) ∧
    (∀ γ : Circle, S (D.rationalU γ) =
      D.rationalSymplecticSplitting (D.rationalDualPairAction γ))

theorem local_covering : ∀ v u,
    counterexampleModel.projection
        (counterexampleModel.includeMp v (counterexampleLocal v u)) =
      counterexampleModel.dualPairAction (counterexampleModel.includeU v u) := by
  intro v u
  rfl

/-- The rational symplectic map really is a section of the projection. -/
theorem rational_section_covers (g : Circle) :
    counterexampleModel.projection
      (counterexampleModel.rationalSymplecticSplitting g) = g := by
  rfl

theorem rational_embedding_injective :
    Function.Injective counterexampleModel.rationalU := by
  intro a b h
  exact h

theorem local_embeddings_injective (v : Unit) :
    Function.Injective (counterexampleModel.includeU v) ∧
    Function.Injective (counterexampleModel.includeMp v) := by
  constructor <;> intro a b h <;> exact h

theorem no_required_splitting :
    ¬ HasRequiredSplitting counterexampleModel counterexampleLocal := by
  rintro ⟨S, _, hFactor, hRational⟩
  have hLocal : S (-1) = (-1, 1) := hFactor () (-1)
  have hGlobal : S (-1) = (-1, -1) := hRational (-1)
  have h : (1 : Circle) = -1 :=
    congrArg Prod.snd (hLocal.symm.trans hGlobal)
  have hComplex := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at hComplex

/-- An interpretation permitted by the bare predicate signature, specialized
to the groups above. This is not the intended mathematical definition. -/
def IsStandardUnitaryDatum
    {F : Type*} [Field F] [NumberField F]
    (_E : Type*) [Field _E] [NumberField _E] [Algebra F _E]
    (_D : CircleModel) (_n _m : ℕ)
    (_ψ : AddChar (NumberField.AdeleRing (𝓞 F) F) ℂ)
    (_χV _χW : PUnit.{1} →ₜ* Circle)
    (_s : ∀ _ : Unit, Circle →ₜ* Circle × Circle) : Prop := True

/-- Every hypothesis in the original theorem schema, with the displayed
interpretation of its undefined predicate and our chosen group types. -/
def EncodedHypotheses
    {F : Type*} [Field F] [NumberField F]
    (E : Type*) [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E]
    (D : CircleModel) (n m : ℕ)
    (ψ : AddChar (NumberField.AdeleRing (𝓞 F) F) ℂ)
    (χV χW : PUnit.{1} →ₜ* Circle)
    (s : ∀ _ : Unit, Circle →ₜ* Circle × Circle) : Prop :=
  Module.finrank F E = 2 ∧
  Continuous ψ ∧
  (∀ a, ‖ψ a‖ = 1) ∧
  (∃ a, ψ a ≠ 1) ∧
  (∀ a : F,
    ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) a) = 1) ∧
  (∀ a, χV (D.classEmbedding a) = D.quadraticCharacter a ^ n) ∧
  (∀ a, χW (D.classEmbedding a) = D.quadraticCharacter a ^ m) ∧
  IsStandardUnitaryDatum E D n m ψ χV χW s ∧
  (∀ v u, D.projection (D.includeMp v (s v u)) =
    D.dualPairAction (D.includeU v u))

/-- For every arithmetic input allowed in AdelicSplitting, the unconstrained interface
admits a model satisfying all encoded hypotheses but not its conclusion. -/
theorem countermodel_for_any_arithmetic_input
    {F E : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2)
    (n m : ℕ)
    (ψ : AddChar (NumberField.AdeleRing (𝓞 F) F) ℂ)
    (hψContinuous : Continuous ψ)
    (hψUnitary : ∀ a, ‖ψ a‖ = 1)
    (hψNontrivial : ∃ a, ψ a ≠ 1)
    (hψRational : ∀ a : F,
      ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) a) = 1) :
    EncodedHypotheses E counterexampleModel n m ψ 1 1 counterexampleLocal ∧
    ¬ HasRequiredSplitting counterexampleModel counterexampleLocal := by
  refine ⟨?_, no_required_splitting⟩
  refine ⟨hQuadratic, hψContinuous, hψUnitary, hψNontrivial,
    hψRational, ?_, ?_, trivial, local_covering⟩
  all_goals intro a; simp [counterexampleModel]

end Specification

/-- The full unconditional AdelicSplitting conclusion for the accepted corrected local normalization. -/
theorem adelic_unitary_splitting_compatible_with_rational_points
    (F : Type) [Field F] [NumberField F]
    (d : F) (hQuadratic : d ≠ 0 ∧ ¬ IsSquare d)
    (n m : ℕ)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (hHermitian : H.val.conjTranspose = H.val)
    (hSkewHermitian : K.val.conjTranspose = -K.val)
    (C : Characters.Construction.GlobalCharacters F d n m)
    (P : Assembly.Construction.GlobalFrames F d n m H K)
    (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hQuadratic.1 C P) :
    (∀ g : Integral.Construction.AdelicDualPair F H.val K.val,
      Vacuum.Construction.globalProjection F (n * m) C.ψ
          (Assembly.Construction.constructedAdelicLift F d n m H K hQuadratic.1 C P D g) =
        Assembly.Construction.adelicDualPairAction F d n m H K hQuadratic.1 C P D g) ∧
    (∀ v (g : Integral.Construction.LocalUnitary F H.val v × Integral.Construction.LocalUnitary F K.val v),
      Assembly.Construction.constructedAdelicLift F d n m H K hQuadratic.1 C P D
          (Integral.Construction.includeUnitaryPlace F H.val K.val v g) =
        Vacuum.Construction.globalInclude F (n * m) C.ψ v (D.atPlace v g)) ∧
    ∃ r : Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) →* Vacuum.Construction.GlobalCover F (n * m) C.ψ,
      (∀ γ a, (γ, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ ↔ r γ = a) ∧
      (∀ γ, Vacuum.Construction.globalProjection F (n * m) C.ψ (r γ) =
        Vacuum.Construction.rationalSymplectic F (n * m) γ) ∧
      (∀ g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val,
        Assembly.Construction.constructedAdelicLift F d n m H K hQuadratic.1 C P D
            (Integral.Construction.rationalPair F H.val K.val g) =
          r (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g)) := by
  by_cases hN : n * m = 0
  · exact ZeroRankCompatibility.Construction.adelic_unitary_splitting_zero_rank F d hQuadratic.1 n m H K C P D hQuadratic.2 hN
  · have hpos : 0 < n * m := Nat.pos_of_ne_zero hN
    exact ⟨Assembly.Construction.constructedAdelicLift_covers F d n m H K hQuadratic.1 C P D,
      Assembly.Construction.constructedAdelicLift_factors F d n m H K hQuadratic.1 C P D,
      RationalCompatibility.Construction.normalized_rational_compatibility F d hQuadratic.1 n m hpos H K C P D
        hQuadratic.2 hHermitian hSkewHermitian⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.No
