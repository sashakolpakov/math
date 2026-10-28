import OAI.AlgebraicGeometry.PELModuli.CMPoints.EstablishedDescent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PrimeChoice
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionLie
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Descent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Density
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Fine
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CompatiblePrime
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentReduction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDecomposition
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDivisibility
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HeightUniqueness
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockFlatness
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Generic
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PointField
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Transport
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralComponents
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockRank
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeHeight
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentHeight
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Products
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HeightOneCounts
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionDuality
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralBlockRank
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionOrdinaryIs
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ZeroPeriod
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryCM
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryIsogeny
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentDescent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalBallPoint
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodOnBall
import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbstractRealization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodRealization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodAction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralModel
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RealizedIsogenies
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Factorization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFromFactorization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HomDescent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexDiagramSpreading
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericIntegralAction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ActionTransport
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticCoefficientEnlargement
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedArithmeticIsomorphisms
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticFieldPointSpreading
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentFieldPoint
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentDiagram
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarFactorTransport
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralOrdinary
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryComponentPrime

/-! # Ordinary Reduction -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-!
This module gives a complete conditional construction of ordinary reduction.

The arithmetic and geometric constructions are native: ring-of-integers
models, adic completions, geometric scheme fibers, actual endomorphism
actions, torsion subfunctors and Cartier characters. HasHeight requires a
representation by the genuine FiniteEtale q-divisible group; it does not assign
height three to an abstract label.

The proof constructs CM points on every supplied component and descends
them using the CM abelian-variety theorems. Their three CM factors, integral
actions, and scalar splitting maps spread over the chosen arithmetic base.
Generic comparisons extend to the fixed PEL family along actual integral CM
sections. Height-one specialization of the factors proves the ordinary counts.

The exact SplitPrimes input chooses one common prime with compatible q-adic
embeddings for every point/model field and all supplied auxiliary fields.
The resulting residue maps give ordinary points in the specified
geometric components. Openness openness and proved component irreducibility
give density. The same prime gives all height-three, conjugate-duality,
and Lie-rank clauses.

The required period comparison on the actual universal PEL family is
proved through local holomorphic period matrices and CM fibers. Finite
Hom descent follows from the full Presentations Hilbert/Hom and endomorphism-equation
inputs with proved rigidity and fixed-model comparison. Positive
multiplication finiteness and canonical Poincare torsion naturality are
proved. CM-point existence, ordinary specialization, and density are
conclusions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- Precisely the Openness openness proposition, with its abelian-scheme hypotheses. -/
def OrdinaryReduction.OpennessInput : Prop :=
  ∀ (q : ℕ) [Fact q.Prime]
    (S : Over (Spec (CommRingCat.of (ZMod q))))
    (A : Over S.left) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom],
    IsOpen {x : S.left | Models.IsOrdinaryAt q A x}

section

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

def Models.RankThreePELModel.GoodIntegralReduction.HasHeight (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) (h : ℕ) : Prop :=
  BlocksProjectors.BlockHasHeight (R.fiberAbelian a x) (R.fiberAction a x)
    (j.localCharacter M.extendedEmbedding τ) h

def Models.RankThreePELModel.GoodIntegralReduction.PolarizationDuality (a : M.Family) (x : R.geom a)
    (τ υ : Gal(E/ℚ)) : Prop :=
  DualityPairing.PolarizationDuality (R.fiberPolarized a x) (R.fiberAction a x)
    (j.localCharacter M.extendedEmbedding τ) (j.localCharacter M.extendedEmbedding υ)

/-- The idempotent block is the actual equalizer scheme, on the geometric fiber. -/
def Models.RankThreePELModel.GoodIntegralReduction.blockScheme (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
    (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) (n : ℕ) :
    Over (Spec (.of (R.fiberField a x))) :=
  BlocksProjectors.idempotentBlockScheme (R.fiberAbelian a x) (R.fiberAction a x)
    (q ^ n) (j.projector M.extendedEmbedding hsplit n τ)

def Models.RankThreePELModel.GoodIntegralReduction.blockGroupScheme (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
    (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) (n : ℕ) :
    CommGrp (Over (Spec (.of (R.fiberField a x)))) :=
  BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit
    (R.fiberAbelian a x) (R.fiberAction a x) n τ

theorem Models.RankThreePELModel.GoodIntegralReduction.blockGroupScheme_underlying (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
    (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) (n : ℕ) :
    (R.blockGroupScheme hsplit a x τ n).X = R.blockScheme hsplit a x τ n := rfl

/-- Openness applies to the constructed geometric reduction over F_q. -/
theorem Models.RankThreePELModel.GoodIntegralReduction.ordinaryLocus_open (hOpenness : OrdinaryReduction.OpennessInput) (a : M.Family) :
    IsOpen (R.ordinaryLocus a) := by
  let A := R.abelian a
  let relativeDimensionA : SmoothOfRelativeDimension (3 * M.s) A.scheme.hom := A.smoothDimension
  have smoothA : Smooth A.scheme.hom := SmoothOfRelativeDimension.smooth (3 * M.s) A.scheme.hom
  exact @hOpenness q inferInstance (R.geometricFiberOverPrimeField a) A.scheme
    A.group A.commutative smoothA A.proper A.connected

end

/-- The topological final step once a component's ordinary point is
constructed. This helper does not assert existence of that point. -/
theorem OrdinaryReduction.dense_open_in_irreducible_component
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (x : X) [IrreducibleSpace (connectedComponent x)]
    (hwitness : ∃ y : connectedComponent x, y.val ∈ U) :
    Dense {y : connectedComponent x | y.val ∈ U} := by
  exact (hU.preimage continuous_subtype_val).dense hwitness

/-- Smoothness of the given model supplies component irreducibility;
Openness then turns a constructed ordinary point into density. -/
theorem OrdinaryReduction.ordinary_dense_on_component_of_point
    (hOpenness : OrdinaryReduction.OpennessInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {M : Models.RankThreePELModel E K} (hM : M.HasPrescribedBallPeriods)
    {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
    (R : M.GoodIntegralReduction q j) (a : M.Family) (x : R.geom a)
    (hwitness : ∃ y : connectedComponent x, R.IsOrdinary a y.val) :
    Dense {y : connectedComponent x | R.IsOrdinary a y.val} := by
  let : IrreducibleSpace (connectedComponent x) := R.connectedComponent_irreducible hM a x
  exact OrdinaryReduction.dense_open_in_irreducible_component (R.ordinaryLocus a)
    (R.ordinaryLocus_open hOpenness a) x hwitness

/-- A constructed finite set of ordinary component points is enough for
the density clause on every geometric connected component. -/
theorem OrdinaryReduction.ordinary_dense_of_finite_component_points
    (hOpenness : OrdinaryReduction.OpennessInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {M : Models.RankThreePELModel E K} (hM : M.HasPrescribedBallPeriods)
    {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
    (R : M.GoodIntegralReduction q j) (a : M.Family)
    (y : ∀ t : Fin (M.componentCount a), (R.geometricComponent a t).left)
    (hy : ∀ t, R.IsOrdinary a ((R.geometricComponentInclusion a t).left (y t))) :
    ∀ x : R.geom a, Dense {z : connectedComponent x | R.IsOrdinary a z.val} := by
  intro x
  exact OrdinaryReduction.ordinary_dense_on_component_of_point hOpenness hM R a x
    (R.ordinary_point_in_component_of_finite_points hM a y hy x)

/-- Separate density assertions imply simultaneous ordinarity when the
finite collection of universal families has a common base. -/
theorem OrdinaryReduction.finite_simultaneous_dense_open
    {X Idx : Type*} [TopologicalSpace X] [Finite Idx]
    (U : Idx → Set X) (hopen : ∀ i, IsOpen (U i)) (hdense : ∀ i, Dense (U i)) :
    IsOpen (⋂ i, U i) ∧ Dense (⋂ i, U i) := by
  refine ⟨isOpen_iInter_of_finite hopen, ?_⟩
  rw [← Set.sInter_range]
  exact (Set.finite_range U).dense_sInter
    (by rintro V ⟨i, rfl⟩; exact hopen i)
    (by rintro V ⟨i, rfl⟩; exact hdense i)

/-- The arithmetic, openness, height, duality, and Lie clauses at one common
prime. The complete theorem below also supplies density.
The torsion finiteness and canonical polarization adjoints are proved from
the actual polarized family. -/
theorem OrdinaryReduction.exists_common_good_reduction_with_block_invariants
    (hOpenness : OrdinaryReduction.OpennessInput) (hSplitPrimes : Arithmetic.SplitPrimesInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {Idx : Type*} [Finite Idx]
    (L : Idx → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      Arithmetic.SplitsCompletelyAt E q ∧ Arithmetic.SplitsCompletelyAt K q ∧
      Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ j : M.QadicChoice q,
        j.HasSplitCoordinates M.extendedEmbedding ∧
        ∃ R : M.GoodIntegralReduction q j,
          (∀ a : M.Family, IsOpen (R.ordinaryLocus a)) ∧
          ∃ chosen : Set Gal(E/ℚ),
            Arithmetic.rationalConjugation E ∈ chosen ∧
            (∀ τ, τ ∈ chosen ↔ Arithmetic.rationalConjugation E * τ ∉ chosen) ∧
            (∀ (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)),
              R.HasHeight a x τ 3 ∧ R.PolarizationDuality a x τ (Arithmetic.rationalConjugation E * τ)) ∧
            (∀ (a : M.Family) (x : R.geom a),
              R.HasLieRank a x (Arithmetic.rationalConjugation E) 1 ∧
              ∀ τ ∈ chosen, τ ≠ Arithmetic.rationalConjugation E →
                R.HasLieRank a x τ 0 ∨ R.HasLieRank a x τ 3) := by
  obtain ⟨D, hD⟩ := M.exists_reduction_height_bound hM
  obtain ⟨q, hq, hb, hx, he, hk, hf, hl, j, hsplit, ⟨R⟩⟩ :=
    PrimeChoice.exists_common_good_split_qadic_prime hSplitPrimes M hM L excluded (max bound D)
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨chosen, hc, hp, hlie⟩ := R.exists_representatives_with_lieRanks hM
  refine ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx, he, hk, hf, hl,
    j, hsplit, R, R.ordinaryLocus_open hOpenness, chosen, hc, hp, ?_, hlie⟩
  intro a x τ
  exact ⟨hD q hq j hsplit (lt_of_le_of_lt (le_max_right _ _) hb) R a x τ,
    R.fiber_polarization_duality hsplit a x τ⟩

/-- The complete conditional ordinary-reduction statement. The CM points, their
ordinary specializations, and density are conclusions of the construction. -/
theorem OrdinaryReduction.exists_completely_split_prime_dense_ordinary
    (hOpenness : OrdinaryReduction.OpennessInput) (hSplitPrimes : Arithmetic.SplitPrimesInput)
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (E K : Type) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    (M : Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    {Idx : Type*} [Fintype Idx]
    (L : Idx → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧
      Arithmetic.SplitsCompletelyAt E q ∧ Arithmetic.SplitsCompletelyAt K q ∧
      Arithmetic.SplitsCompletelyAt M.arithmetic.extension.carrier q ∧
      (∀ i, Arithmetic.SplitsCompletelyAt (L i) q) ∧
      ∃ j : M.QadicChoice q,
        j.HasSplitCoordinates M.extendedEmbedding ∧
        ∃ R : M.GoodIntegralReduction q j,
          (∀ a : M.Family, IsOpen (R.ordinaryLocus a) ∧
            ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val}) ∧
          ∃ chosen : Set Gal(E/ℚ),
            let c := (NumberField.IsCMField.complexConj E).restrictScalars ℚ
            c ∈ chosen ∧ (∀ τ, τ ∈ chosen ↔ c * τ ∉ chosen) ∧
            (∀ (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)),
              R.HasHeight a x τ 3 ∧ R.PolarizationDuality a x τ (c * τ)) ∧
            (∀ (a : M.Family) (x : R.geom a),
              R.HasLieRank a x c 1 ∧
              ∀ τ ∈ chosen, τ ≠ c → R.HasLieRank a x τ 0 ∨ R.HasLieRank a x τ 3) := by
  obtain ⟨D, hD⟩ := M.exists_reduction_height_bound hM
  obtain ⟨q, hq, hb, hx, hE, hK, hBase, hL, j, hsplit, R, hpoints⟩ :=
    OrdinaryComponentPrime.exists_common_good_split_prime_with_ordinary_component_points hSplitPrimes hHilb hEnd EstablishedDescent.abelian_descent EstablishedDescent.moduli_descent
      M hM L excluded (max bound D)
  let : Fact q.Prime := ⟨hq⟩
  choose y hy using hpoints
  obtain ⟨chosen, hc, hp, hlie⟩ := R.exists_representatives_with_lieRanks hM
  refine ⟨q, hq, lt_of_le_of_lt (le_max_left _ _) hb, hx, hE, hK, hBase, hL, j, hsplit, R,
    fun a => ⟨R.ordinaryLocus_open hOpenness a,
      OrdinaryReduction.ordinary_dense_of_finite_component_points hOpenness hM R a (y a) (hy a)⟩,
    chosen, hc, hp, ?_, hlie⟩
  intro a x τ
  exact ⟨hD q hq j hsplit (lt_of_le_of_lt (le_max_right _ _) hb) R a x τ,
    R.fiber_polarization_duality hsplit a x τ⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
