import OAI.Analysis.HodgeTheory.Decomposition.Correction
import OAI.Analysis.HodgeTheory.Decomposition.Form
import OAI.Analysis.HodgeTheory.Decomposition.AdjointAlgebra
import OAI.Analysis.HodgeTheory.Decomposition.SymbolEllipticity
import OAI.Analysis.HodgeTheory.Decomposition.EnergyDomain
import OAI.Analysis.HodgeTheory.Decomposition.AdjointLocality
import OAI.Analysis.HodgeTheory.Decomposition.AdjointCoefficients
import OAI.Analysis.HodgeTheory.Decomposition.WeakResolvent
import OAI.Analysis.HodgeTheory.Decomposition.Coordinate
import OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp
import OAI.Analysis.HodgeTheory.Decomposition.Multiplication
import OAI.Analysis.HodgeTheory.Decomposition.Multiplier
import OAI.Analysis.HodgeTheory.Decomposition.ChartLocalization
import OAI.Analysis.HodgeTheory.Decomposition.FrozenEstimate
import OAI.Analysis.HodgeTheory.Decomposition.FreezingError
import OAI.Analysis.HodgeTheory.Decomposition.GradientEnergy
import OAI.Analysis.HodgeTheory.Decomposition.ManifoldGarding
import OAI.Analysis.HodgeTheory.Decomposition.LocalRellich
import OAI.Analysis.HodgeTheory.Decomposition.WeakEquation
import OAI.Analysis.HodgeTheory.Decomposition.EnergyLocalization
import OAI.Analysis.HodgeTheory.Decomposition.VectorSobolevDensity
import OAI.Analysis.HodgeTheory.Decomposition.VectorElliptic
import OAI.Analysis.HodgeTheory.Decomposition.VectorEnergyLocalization
import OAI.Analysis.HodgeTheory.Decomposition.GardingExtension
import OAI.Analysis.HodgeTheory.Decomposition.VectorLocalElliptic
import OAI.Analysis.HodgeTheory.Decomposition.ChartTestDifferentials
import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzEnergy
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveFluxSobolev
import OAI.Analysis.HodgeTheory.Decomposition.SmoothChartForcing
import OAI.Analysis.HodgeTheory.Decomposition.WeakNeighborhood
import OAI.Analysis.HodgeTheory.Decomposition.WeakSmoothNeighborhood
import OAI.Analysis.HodgeTheory.Decomposition.SmoothHarmonic
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveSharpDerivative
import OAI.Analysis.HodgeTheory.Decomposition.LefschetzSymbol
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveMetricCompatibility
import OAI.Analysis.HodgeTheory.Decomposition.BilinearSymbolAdjoint
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveDensityDerivative
import OAI.Analysis.HodgeTheory.Decomposition.ConnectionSymbolTrace
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantCodifferential
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveKahlerCommutator
import OAI.Analysis.HodgeTheory.Decomposition.TwistedDolbeault
import OAI.Analysis.HodgeTheory.Decomposition.ExteriorConstantBracket
import OAI.Analysis.HodgeTheory.Decomposition.LefschetzRotation
import OAI.Analysis.HodgeTheory.Decomposition.ComponentRotationCharts
import OAI.Analysis.HodgeTheory.Decomposition.ComponentLaplacian
import OAI.Analysis.HodgeTheory.Decomposition.ComponentRotation
import OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonicTypes
import OAI.Analysis.HodgeTheory.Decomposition.BettiFiltration

/-! # Constructions -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Constructions

noncomputable section

/-!
HodgeDecomposition proof assembly. HodgeDecompositionCore proves conjugation and basic filtration results.
Types, Multilinear, Pointwise, Projectors, and SmoothDecomposition
prove the full type decomposition of genuine smooth forms in every degree.
Dolbeault, Filtration, and Correction prove filtered differential and
correction identities. The metric modules construct the positive global
pointwise form pairing from the actual projective Kähler metric and prove
orthogonality of distinct bidegrees. The inverse-Gram coordinate formula proves
smoothness of the metric coefficients and continuity of the global pairing.
The volume modules construct the actual finite full-support metric measure;
FormL2 constructs the positive L² pairing and embeds genuine smooth forms
injectively and densely in its Hilbert completion.
The adjoint modules construct a genuine global complex-linear codifferential,
prove its complex L² adjoint identity and square-zero law, and construct the
Hodge Laplacian. Its kernel is exactly the closed and coclosed smooth forms;
exact harmonic forms vanish.
The actual Hilbert energy domain embeds injectively and densely into L².
Every chart has the explicit codifferential formula; the exterior symbol is
exact at nonzero covectors and its metric Hodge energy is positive.
The symbol energy is uniformly coercive on compact chart sets. The regularized
weak equation has a unique bounded solution in the actual energy domain, with
a positive symmetric L² resolvent. Coordinate L² norms of supported forms are
uniformly controlled by their actual manifold L² norms.
Chart localization is a bounded map on the completed L² space, and supported
forms also satisfy the reverse norm comparison. The frozen operators have
their actual complex Fourier symbols; weighted Plancherel and symbol
coercivity give the first-order frozen energy estimate.
The Fourier moment is the actual gradient energy. The local codifferential
has smooth first-order and zero-order coefficient operators, with a proved
squared freezing-error bound and arbitrarily small local principal error.
Absorbing the integrated coefficient error gives a genuine local Gårding
estimate in the manifold L² norms of a, da, and d*a. Both actual Hodge
differentials preserve support and agree with the Schwartz chart operators.
Finite-dimensional coefficient Rellich compactness and the two coordinate
norm comparisons prove local manifold L² compactness for graph-bounded
smooth forms supported in sufficiently small chart subsets.
Explicit cutoff commutators are bounded in L², so cutoff multiplication is
bounded in the Hodge graph norm. A finite real partition proves global
Rellich compactness and compactness of the actual completed energy inclusion.
The actual weak harmonic kernel is finite dimensional. Its L² projection and
the unique normalized weak Poisson solution for the orthogonal remainder are
constructed without a solvability assumption. Every energy-domain element
has actual vector-valued local H¹ coefficients. The genuine vector
difference-quotient criterion and a second-derivative theorem for weak systems
under an integrated Gårding estimate are proved. The actual smooth Hodge
principal coefficient has a bounded Lipschitz local extension with the required
integrated coercivity, proved from its genuine frozen Fourier estimate.
Vector cutoff calculus and interior H² regularity include the lower-order
H¹ flux. Compactly supported Euclidean test forms lift uniquely to genuine
global smooth forms, with both differential and weighted pairing identities.
The actual smooth complex lower-order coefficients give the exact Hodge energy
expansion, and the localized flux has proved H¹ regularity on energy inputs.
The bounded chart test extension and its adjoint give genuine local L²
forcing, with an explicit smooth representative for smooth global forcing.
The completed manifold weak equation is proved to be the actual local vector
equation, including all lower-order terms. Every chart point has compatible
cutoffs and a proved coercive extension, giving unconditional interior H²
regularity for actual weak Hodge solutions with L² forcing.
Strong vector derivative limits and differentiation of the actual weak flux
equation give elliptic regularity at every Sobolev order. Nested cutoffs
preserve the full local Hodge energy, so smooth manifold forcing gives
unconditional smooth local representatives of actual energy-domain solutions.
Bounded chart reconstruction, compact smooth coefficient representatives,
and a finite partition of unity give global smooth regularity. Every weak
harmonic form and every weak Green solution with smooth forcing is proved
smooth. The actual smooth Hodge decomposition and existence and uniqueness
of harmonic representatives of closed forms follow. The positive-degree
harmonic space is canonically isomorphic to the genuine de Rham form quotient.
The actual metric derivatives construct smooth torsion-free connection
coefficients that preserve the metric and complex structure. The induced
connection on genuine covectors preserves each pure type, and its alternation
is the actual exterior derivative. The inverse-metric derivative and the
principal inverse-Kähler-bivector commutator are proved. The induced form
metric is coordinate invariant, jointly smooth, and compatible with the actual
connection. Exterior multiplication is adjoint to inverse-metric insertion.
Jacobi’s formula gives the actual metric-volume derivative; torsion-free
coefficients give the full exterior-symbol trace cancellation. Differentiating
the density-weighted pairing identifies the actual coordinate adjoint, including
all lower-order terms. The genuine global codifferential equals the negative
metric trace of the constructed covector connection in every chart. Inverse
Kähler contraction is smooth and parallel. Its full local commutator with the
twisted exterior derivative equals the actual global codifferential, including
the degree-one boundary case. The twisted derivative is exactly i times the
difference of the actual Dolbeault derivatives. Constant-direction exterior
derivatives square to zero and anticommute by symmetry of the actual second
Fréchet derivative. Infinitesimal complex rotation commutes with inverse
Kähler contraction and has distinct eigenvalues on the genuine smooth
bidegrees. Its global component operator has the exact local covector formula.
The ordinary and twisted exterior rotation commutators are proved. The full
Kähler bracket anticommutes with its differential, including the boundary
degree. These identities prove that the actual global componentwise Hodge
Laplacian commutes with rotation and preserves every genuine smooth bidegree
in every positive degree. It consequently commutes with the smooth type
projectors, so every harmonic family is a sum of harmonic pure-type families.
Every actual Betti class has a unique harmonic representative. The prescribed
Hodge pieces are precisely the images of pure harmonic families and form an
internal direct sum. The harmonic representative of a filtered closed form
is filtered, which proves the reverse filtration inclusion. Together with
the actual closed-form conjugation and the degree-zero argument, this proves
the full HodgeDecomposition statement below with only the prescribed variety and degree.
-/

/-- Hodge decomposition, actual closed-form conjugation, and the de Rham
filtration for every smooth projective complex presentation and every degree. -/
theorem hodge_decomposition_and_filtration
    (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    DirectSum.IsInternal (Core.Constructions.hodgePiece X n) ∧
    (∃ c : X.complexCohomology n →ₛₗ[starRingEnd ℂ]
        X.complexCohomology n,
      Function.Involutive c ∧
      (∀ ω : X.componentClosedForms n,
        c (X.closedFormBettiClass n ω) =
          X.closedFormBettiClass n (Core.Constructions.conjugateClosed X n ω)) ∧
      (∀ (i : Core.Constructions.Bidegree n) (x : X.complexCohomology n),
        x ∈ Core.Constructions.hodgePiece X n i ↔
          c x ∈ Core.Constructions.hodgePiece X n (Core.Constructions.swapBidegree i))) ∧
    (∀ p : ℤ,
      Core.Constructions.deRhamFiltrationBetti X n p =
        ⨆ (i : Core.Constructions.Bidegree n) (_ : p ≤ (i.val.1 : ℤ)),
          Core.Constructions.hodgePiece X n i) := by
  let : ∀ C : irreducibleComponents X.carrier,
      MeasurableSpace (X.componentVariety C).analyticSpace :=
    fun C => borel (X.componentVariety C).analyticSpace
  let : ∀ C : irreducibleComponents X.carrier,
      BorelSpace (X.componentVariety C).analyticSpace := fun _ => ⟨rfl⟩
  cases n with
  | zero => exact ⟨Core.Constructions.hodge_decomposition_zero X, Core.Constructions.conjugation_clause X 0, Core.Constructions.filtration_zero X⟩
  | succ n => exact ⟨ComponentHarmonicClasses.Constructions.hodge_decomposition_positive X n,
      Core.Constructions.conjugation_clause X (n + 1), BettiFiltration.Constructions.filtration_positive X n⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.Constructions
