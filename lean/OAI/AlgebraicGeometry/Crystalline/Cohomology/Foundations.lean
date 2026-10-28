import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.WittVector.Isocrystal
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Span.Basic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Polynomial
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Contraction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PoincareExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifting
import OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeOne
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicFrames
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothFrames
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Resolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Derived
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPoincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Poincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialUniversal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopePoincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialPoincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Homotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafContraction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SheafExactness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Resolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralUniversal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.AugmentationPowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Universal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Poincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialThickening
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialDerived
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialEval
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.FrameResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Linearization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Localization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Covers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Pullbacks
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.ModuleLocalization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.CechExactness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PrincipalForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Slice
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.CechAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Adjunction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Topology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CoverLifting
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.SheafExactness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerDiagram
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.StructureSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveRestrictions
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.SheafCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeLimitExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafCechAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.DegreeZero
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.ProductLift
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.ZeroDifferential
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FirstDerivedVanishing
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ShortExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.TupleCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedVanishing
import OAI.AlgebraicGeometry.Crystalline.Cohomology.EmptyFrame
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.GlobalAcyclic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.SectionComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeQuotientForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivativeMaps
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PDDerivatives
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.EvaluationDerivative
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.Affine
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.RationalComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Integral
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ResidualCocontinuity
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.DerivedSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperAffineCharts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteScalarExtension
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechBicomplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechTotal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.GlobalSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.InjectiveFlasque
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechSectionCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Coordinate
import OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineDerivedSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Frobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.PolynomialAbsoluteFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.OrdinaryPDForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Rational
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Evaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.RationalFrameFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.CoefficientComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameMaps
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.FunctorMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.AugmentationFormula
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicExtComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameGlobalAcyclic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSectionComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentationZero
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.BigAffine
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusFrames
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistRelativeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.PositiveNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.TransportNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedPolynomial
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusMorphism
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobeniusCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGenerators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafSectionHomEquiv
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.RationalFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittStandardEtaleLift
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothProperTermFinite
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperDeRhamCechFiniteness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusDifferential
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialProjection
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Poincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableZero
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTensor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariablePoincare

/-! # Foundations -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Foundations

noncomputable section

/-!
# Cohomology: global cohomology constructions and comparison foundations

This file implements part of the previously proposed interface, with actual
complete DVRs, Witt vectors, fraction fields, scheme fibres, the crystalline
site, and the global algebraic de Rham complex in its generators-and-relations
presentation, identified with exterior Kähler form sheaves in characteristic
zero. Čech complexes and their augmentation maps are also constructed.
Local Čech contractions and the divided-power de Rham complex are checked.
Relative divided-power envelopes are constructed with their universal
property, reduction, and nilpotent affine thickenings. Affine crystalline
objects map to polynomial frames modulo positive powers of p.
Smooth affine charts lift across the actual elementwise-nilpotent
crystalline kernels, by finite presentation and formal smoothness.
Every crystalline object over such a chart maps to a p-power level of
its PD-envelope tower, preserving the specified residual restriction.
For an affine residual scheme, tuples of maps into the fixed smooth
frame give a canonical resolution of the native constant coefficient
sheaf; its augmentation is a quasi-isomorphism in every degree.
This identifies the native crystalline Ext groups with derived morphisms
from the frame resolution, naturally in the coefficient sheaf.
The envelope's PD one-forms are identified with base-changed Kähler
differentials using the proved unique extension of derivations.
Compatible sections in the p-power frame tower carry divided powers and
surject onto the residual algebra.
Their compatible differential forms define the completed PD de Rham
complex, whose degree-zero term is the inverse-limit ring.
The rank-one divided-polynomial algebra has its actual PD structure and
one-form module; its augmented de Rham sequence is short exact and its
higher PD forms vanish, also after adic completion.
The universal polynomial PD envelope is proved isomorphic to that algebra,
and these exactness results transfer to its actual differential forms.
The local contraction also descends modulo base sub-DP ideals. Over the
Witt ring, the resulting p-power quotients form actual crystalline
thickenings with compatible primitives. Their inverse-limit de Rham
sequence is short exact with constants W(k), and its higher forms vanish.
Its actual completed complex is homotopy equivalent to W(k) in degree
zero; the constructed augmentation is a quasi-isomorphism.
Čech cochains are also assembled as presheaf and sheaf complexes, with
natural augmentations and local sheaf homotopy equivalences on cover members.
The global Čech complex restricts to those local complexes, compatibly
with the canonical augmentation. The augmentation is a quasi-isomorphism
for every open cover: degree-zero cohomology is the coefficient sheaf
and positive homology sheaves vanish globally.
For polynomial PD envelopes over arbitrary coefficient rings, coordinate
differentials form a basis of PD one-forms. Their coordinate derivatives
commute and agree with polynomial partial derivatives. Increasing coordinate
symbols form a basis in every degree, giving an integral exterior-power
description and vanishing above the number of variables.
The actual multivariable divided-power algebra has unique divided-monomial
coefficients over an embedded characteristic-zero base. Its relative DP
structure and universal property, including maps to torsion targets, are
proved; it is identified with the polynomial PD envelope of the base ideal
and all coordinates. The relative PD construction and its universal
property also cover zero base ideals and proper augmentation ideals.
Coefficient changes act on the actual free divided-power algebra and
preserve divided monomials. Divided powers on an augmentation kernel
descend through arbitrary coefficient quotients, including torsion rings.
The actual free divided-power algebra over every commutative ring carries
augmentation divided powers, with the expected coordinate operations and
the unique PD-map universal property, without a torsion-freeness assumption.
Its divided monomials form a basis over every commutative ring. Its
identification with the polynomial PD envelope gives actual coordinate
derivations and integral primitives. In finitely many variables its actual
PD de Rham complex contracts onto the coefficient ring in degree zero,
including over rings with torsion.
Every PD ring has a constructed surjective PD presentation by an integral
domain of characteristic zero. Relative divided powers descend through
the coefficient kernel, yielding the full free relative PD algebra and
its universal property over arbitrary PD bases. Its actual relative
de Rham complex contracts onto the base ring. Adjoining divided coordinates
to any actual affine crystalline thickening produces another crystalline
object; its coefficient inclusion and augmentation preserve divided powers,
and its actual relative form complex has the proved Poincaré contraction.
The polynomial extension is a functor on the native crystalline site,
with natural coordinate derivatives, primitives, projection, and zero
section. Its coordinate complex resolves the original crystalline
functions presheaf. Exact coefficient lifting and sheafification give
a quasi-isomorphic resolution of the native crystalline structure sheaf.
The resulting derived isomorphism expresses the existing crystalline
Ext groups as derived morphisms into this coordinate resolution.
For polynomial variables with arbitrary chosen lifts in the coefficient
ring, the ideal generated by the base reduction kernel and the coordinate
differences is the exact polynomial reduction kernel. Its actual PD
envelope is isomorphic to the relative free divided-power algebra, and
its actual relative differential forms have the Poincaré contraction.
Finite polynomial Witt presentations are constructed for every finite-type
residue algebra. Every native affine chart of the actual smooth special
fibre is a smooth residue algebra and maps, with its prescribed residue
map, to a constructed finite polynomial frame. Its coefficient Čech
resolution therefore needs no separately supplied smooth presentation.
Changes between chosen lifts of fixed residue coordinates define affine
PD transition maps on the actual frame extensions. They compose, preserve
reductions and total polynomial coordinates, and commute with coordinate
differentiation. Objectwise primitives give a natural frame resolution of
the native structure sheaf and an equivalence from its existing crystalline
Ext groups. The frame algebra is identified with the actual PD envelope
of the canonical polynomial reduction kernel. These constructions apply
to the finite Witt frame of every actual smooth residue chart.
Ordinary polynomial de Rham forms have an integral coordinate description,
including their differential. Their maps into the frame resolution are
natural before and after sheafification. In every degree the native frame
resolution term is identified with the scalar extension of those actual
ordinary forms along the fixed polynomial frame map.
The actual free divided-power algebra commutes with tensor base change
and coefficient localization. Translation by coefficient PD-ideal elements
is a PD automorphism, so the native affine frame maps preserve coefficient
localizations even when their chosen coordinate origins differ.
Divided powers are constructed on arbitrary localized ideals by their
fraction formula and uniquely preserve compatibility with the original
PD ring. This constructs principal-open restrictions of actual crystalline
thickenings, preserving the exact reduction kernel and Witt-base data.
Coefficients generating the unit ideal give covers in the native topology.
The principal-open projections are monomorphisms, have the expected
factorization property, and form actual pullback squares under every
native crystalline morphism.
Frame extension preserves these actual principal-open covers. Each
coordinate form term localizes as a module over the original ambient
coefficient ring, and its localization map agrees with the actual
transition map of the native frame resolution after restricting to Witt scalars.
Every generating native cover has an actual principal-open refinement.
The resulting principal-open basis is proved to characterize the full
native crystalline topology. Forgetting lifted frame coordinates and the
native frame functor are continuous and lift every covering sieve.
Their adjoint functors on Witt-module sheaves are both exact. The
sheafified native frame functions identify canonically with the frame
pushforward of the restricted structure sheaf. The adjunction passes to
the actual derived categories and carries the original rank-one
coefficient sheaf to the framed rank-one coefficient sheaf, identifying
derived global sections of framed complexes with those of their pushforwards.
The actual p-power polynomial-envelope levels carry their specified
frame coordinates. The PD universal property makes each level terminal
among framed objects killed by that power of p. The levels form a final
countable tower, so ordinary framed global sections are the inverse limit
of their sections on the tower. This applies to the constructed finite
Witt presentation of every finite-type residue algebra.
The original ambient-function presheaf satisfies the full native sheaf
condition by principal fraction gluing and separation. Its canonical
sheafification isomorphism gives concrete sections of the original
structure sheaf. Ordinary framed global sections of that structure
sheaf are identified with the existing completed PD-envelope ring.
The native and framed Witt-module sheaf categories have constructed
Grothendieck abelian structures and enough injectives.
The native principal Čech augmentation identifies ordinary sections with
degree-zero cocycles on every unit-ideal principal cover. First Čech
vanishing corrects local lifts to gluable cocycles, giving surjectivity
on sections in short exact sequences with such a kernel. Applied to the
actual frame-resolution terms, Čech exactness and injective cycle sequences
prove vanishing of all positive right-derived evaluations at every native
crystalline object. The same section
lifts make the associated Čech sequences short exact in every degree.
The native principal Čech nerve also gives a chain complex of free
representable sheaves. Evaluation identifies its generators with tuples
of lifts of a fixed native base arrow. A fibrewise extra degeneracy
contracts that tuple diagram, proving positive-degree exactness before
and after native sheafification.
Its additive dual is identified with the actual native Čech complex,
proving Čech acyclicity of injective sheaves. The homology sequence and
the constructed injective cycle tower give the higher derived vanishing.
An empty-coordinate frame identifies the original native structure sheaf
with its degree-zero frame term, giving the same positive derived vanishing.
The coordinate framings of each native object form a final discrete
subcategory for left Kan extension. Exact module coproducts make the
left adjoint of framed restriction exact; restriction therefore preserves
injectives. Native injective resolutions then prove positive derived
evaluation vanishing for the original structure sheaf on the framed site.
On the actual p-power envelope tower, injective sections and structure
sections have surjective transitions. Recursive lifting of compatible
sections makes all injective cycle sequences exact after framed global
sections, proving positive derived global vanishing for its structure
sheaf. The rank-one adjunction and injective representatives transfer
this to the original Ext groups. The exact native frame adjunction and
finite exterior-coordinate splittings then prove global acyclicity of
every actual finite frame-resolution term. The coefficient-linear
acyclic-resolution comparison identifies its ordinary section-complex
homology with the original affine integral crystalline cohomology.
For an arbitrary polynomial Witt presentation, its envelope coordinate
derivatives descend to the original p-power frame rings and satisfy their
actual divided-power rule. The coordinate form bases identify every
finite-level PD complex with its tensor coordinate complex, naturally
along the original quotient transitions. Finite free tensor interchange
extends this to an isomorphism with the original completed PD de Rham
complex, including the differential. The PD universal chain rule also
intertwines evaluation into each native free frame with its actual
coordinate differential. Identifying the full section complex with this
completed complex follows by the native frame-function limit, finite
free tensor preservation, and the canonical sheaf section isomorphisms.
The resulting complex isomorphism computes original affine integral
crystalline cohomology by the original completed PD de Rham complex in
every degree. The constructed finite Witt presentation specializes this
to every finite-type residue algebra without an additional hypothesis.
Flat scalar extension with the original Witt action commutes with homology,
so the rational affine comparison computes the original crystalline
cohomology over the Witt fraction field by the same completed complex.
The original completed forms vanish above the number of coordinates,
giving the corresponding integral and rational affine cohomology bound.
Open immersions induce fully faithful native site embeddings preserving
and lifting all covers. Their exact sheaf restrictions preserve injectives
and identify the original coefficient and structure sheaves. Residual
opens define a cocontinuous functor to the special fibre's Zariski site.
Its actual right Kan direct image has sections naturally identified with
crystalline global sections on each open subscheme; this identifies the
whole restricted injective-resolution complex and its derived sections.
Properness supplies a finite affine cover with finite-type coordinate
rings, so every chart carries the proved completed-complex computation.
Finite free coefficient extension preserves limits of the original large
modules. An explicit extension-ring-linear isomorphism commutes with
evaluation of compatible systems. Applied to the original completed PD
forms, it identifies the whole coefficient-extended complex with the
complex of compatible extended forms, including the actual differential.
The standalone good-reduction base modules prove that the specified DVR
is p-adically complete and finite free over its Witt embedding, and that
its original generic field is finite over the original Witt fraction field.
Thus integral completion base change applies for arbitrary ramification.
Čech sheaf descent also holds with independent scheme and coefficient
universes, using exact sheafification for the native lifted Witt modules.
Its canonical augmentation resolves the actual crystalline Zariski direct
image on every open cover, including the finite proper affine cover.
Functoriality in the coefficient sheaf gives a double complex from the
original native injective resolution, with quasi-isomorphic augmented rows.
Exact conservative Zariski fibers prove that the canonical map to its
first-quadrant total complex is a quasi-isomorphism in every degree.
The native Zariski direct image has an exact inverse-image left adjoint
and therefore preserves injectives. Its global sections are naturally
the native crystalline global sections; this identifies the full
section complexes and their derived cohomology for the original resolution.
Injective native-size module sheaves extend sections across opens.
Open restriction and open direct image preserve injectives, so the finite
Čech terms of an injective sheaf form an injective resolution. Comparing
with its trivial resolution proves exactness after global sections.
Finite sums in each total degree give the canonical total comparison after
global sections. Coefficient-linear adjunction identifies these sections
with the original integral crystalline Ext groups, and flat Witt
fraction-field extension gives the original rational groups.
Every Čech intersection of the actual proper affine cover is affine and
has finite-type coordinates with the proved completed affine computation.
The Čech intersection presheaves are already sheaves; their canonical
sheafification units identify the full complexes with their original
presheaf cochains, and global sections give the usual intersection cochains.
These coordinate isomorphisms are natural in the coefficient sheaf, so
they identify both differentials of the original section double complex.
Its total intersection cochains compute the specified integral and rational
crystalline groups. Derived Zariski sections on each proper Čech
intersection identify with its original completed affine computation.
Ordinary polynomial forms over the Witt ring have integral coordinate
primitives at weights prime to p. Their successive homotopies project
onto exactly the monomial forms with every coordinate weight divisible
by p. Explicit raising and lowering maps identify these retained weights.
The actual polynomial substitution x_i ↦ x_i^p acts in degree n as p^n
times weight raising. With N variables its integral transfer has both
composites equal to p^N times the identity up to the constructed homotopy.
Applying integral p-adic completion and then extending to the original
Witt fraction field gives a homotopy inverse. This proves a quasi-isomorphism
for that substitution on the completed original polynomial de Rham complex.
Semilinear change of coefficients acts on the original differential
symbols and commutes with their differential. Ring equivalences give
actual complex isomorphisms, also after compatible integral completion.
The Witt-coefficient Frobenius therefore remains an isomorphism after
completion and extension to the original Witt fraction field. Composing
with polynomial substitution gives the explicit semilinear cohomology
operator and proves its bijectivity for the completed polynomial complex.
The underlying integral polynomial lift reduces to absolute Frobenius;
its factorization on differential symbols survives completion and agrees
with the rational operator on elementary tensors.
For the actual presentation W(k)[x] → k[x], the kernel is (p).
Its specified base-compatible relative PD envelope is canonically W(k)[x].
The ordinary and base-PD polynomial forms agree integrally. The original
p-power crystalline frame limit is the integral adic module completion;
the equivalence intertwines the original coordinate derivatives.
Finite exterior powers identify the completed ordinary polynomial complex
with the actual completed PD frame complex. After the prescribed universe
lifts this computes the original integral crystalline Ext; flat extension
to the original Witt fraction field computes the original rational groups.
The comparison evaluates every ordinary polynomial form by the original
frame algebra map, including all differential symbols.
The absolute-Frobenius lift preserves the actual envelope divided powers,
descends to every original p-power frame, and defines a semilinear chain
map on their completed PD forms. Semilinear completion density extends
the comparison's Frobenius compatibility from finite forms to the whole
completed complex. After original Witt fraction-field extension, the
actual completed frame Frobenius is a quasi-isomorphism, and its explicit
cycle-quotient cohomology map is bijective.
The affine frame-section complex now carries a proved map representing
the original geometric crystalline Frobenius. Geometric pullback and
the actual power-coordinate PD map preserve the original augmentation.
Inverse coefficient restriction cancels the crystalline base twist,
which is an exact equivalence of the original sheaf categories.
The resulting frame isomorphism transports the proved acyclicity of
the generating frame terms. The all-degree comparison identifies the
composed section map with the original big-site Frobenius on Ext.
Transport through the actual completed-PD comparison gives a completed
chain map representing that original Frobenius. The explicit polynomial
lift is expressed in the same coefficient modules. At every polynomial
level it defines a big crystalline morphism over Frobenius and raises
each canonical coordinate to its pth power. Actual sheaf representatives,
the relative-form coordinate square, and finite-level evaluation prove
equality of these two completed operators. The canonical exact-functor
homology comparison and compatible scalar extension identify the original
integral and rational crystalline Frobenius with the polynomial operator.
Thus the original rational crystalline Frobenius of polynomial affine
space is bijective over the original Witt fraction field.
The constructed standard etale Witt lifts also apply over arbitrary
perfect residue fields. Their reduction has kernel (p), they are smooth
and flat over the Witt ring, and their ordinary form complexes compute
the original bounded crystalline cohomology.
The ordinary form sheaves are quasicoherent and of finite type on the
actual smooth proper etale-coordinate cover over any field. Proper
coherent cohomology and coefficient-linear Cech comparison give finite
cohomology of their de Rham Cech total. In characteristic zero, exact
integer coefficient restriction identifies the original coefficient Ext
with additive sheaf cohomology, preserving the canonical field action.
The actual successive Hodge truncations have single-term quotients.
Their distinguished triangles and the vanishing of the final connective
tail prove finiteness of the original de Rham hypercohomology in every
degree. This applies to the actual generic fiber without projectivity
or a ramification restriction.
The actual acyclic-resolution comparison is natural for maps of augmented
resolutions in every degree. This follows from naturality of the original
Ext connecting maps, the canonical cycle sequences, and their iterated
dimension shifts, including all cohomological degree transports.
Each coordinate has an actual integral primitive on that multivariable
algebra. Differentiation and integration satisfy both splitting identities;
the primitive and coordinate-constant projection commute with derivatives
in the other coordinates.
Exterior multiplication and contraction assemble those primitives into
a homotopy equivalence from the multivariable tensor exterior complex
to the coefficient ring in degree zero. The coordinate tensor description
is proved isomorphic to the actual multivariable PD de Rham complex,
including its differential. The resulting actual PD complex is homotopy
equivalent to the coefficient ring in degree zero, and its constructed
augmentation is a quasi-isomorphism.
Modulo every base sub-DP ideal L, the coordinate derivations and
primitives descend, the actual quotient one-forms retain their coordinate
basis, and the actual multivariable PD complex contracts onto R/L.
Reduction commutes with the coordinate operators, constants, and tensor
form descriptions. Over W(k), the multivariable p-power quotients form
actual crystalline thickenings and an inverse system. Finite free tensor
interchange identifies the tensor complex of compatible sections with
the actual inverse-limit PD form complex, including its differential.
The resulting completed multivariable crystalline form complex is
homotopy equivalent to W(k) in degree zero, with a quasi-isomorphic
augmentation and degree-zero cohomology W(k).
It does not import the admitted statement specification.
The Hodge filtration is induced by the degree truncations of this complex.
The global comparison, rational crystalline finiteness, and bijectivity
of crystalline Frobenius in the general smooth proper case remain unproved. The native Frobenius and
pullback operators are constructed in GoodReductionOperators.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The arithmetic base of good reduction. The Witt-vector embedding must
induce the identity on the specified residue field. No cohomology or
comparison property is included in this structure. -/
structure MixedCharacteristicDVR (p : ℕ) [Fact p.Prime] where
  R : Type u
  [ringR : CommRing R]
  [domainR : IsDomain R]
  [dvrR : IsDiscreteValuationRing R]
  [charZeroR : CharZero R]
  [completeR : IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  k : Type u
  [fieldk : Field k]
  [charPk : CharP k p]
  [perfectk : PerfectRing k p]
  residueEquiv : IsLocalRing.ResidueField R ≃+* k
  wittLift : WittVector p k →+* R
  wittLift_injective : Function.Injective wittLift
  wittLift_residue :
    (residueEquiv.toRingHom.comp (IsLocalRing.residue R)).comp wittLift =
      WittVector.constantCoeff

attribute [instance] MixedCharacteristicDVR.ringR MixedCharacteristicDVR.domainR
  MixedCharacteristicDVR.dvrR MixedCharacteristicDVR.charZeroR
  MixedCharacteristicDVR.completeR MixedCharacteristicDVR.fieldk
  MixedCharacteristicDVR.charPk MixedCharacteristicDVR.perfectk

namespace MixedCharacteristicDVR

variable {p : ℕ} [Fact p.Prime] (B : MixedCharacteristicDVR.{u} p)

/-- The fraction field of the complete DVR. -/
abbrev K := FractionRing B.R

/-- The fraction field of the Witt vectors of the perfect residue field. -/
abbrev K₀ := FractionRing (WittVector p B.k)

/-- The specified residue-field map. -/
def reduction : B.R →+* B.k :=
  B.residueEquiv.toRingHom.comp (IsLocalRing.residue B.R)

theorem reduction_surjective : Function.Surjective B.reduction :=
  B.residueEquiv.surjective.comp IsLocalRing.residue_surjective

@[simp]
theorem reduction_eq_zero_iff (r : B.R) :
    B.reduction r = 0 ↔ r ∈ IsLocalRing.maximalIdeal B.R := by
  change B.residueEquiv (IsLocalRing.residue B.R r) = 0 ↔ _
  rw [map_eq_zero_iff _ B.residueEquiv.injective,
    IsLocalRing.residue_eq_zero_iff]

@[simp]
theorem reduction_wittLift (w : WittVector p B.k) :
    B.reduction (B.wittLift w) = w.coeff 0 :=
  DFunLike.congr_fun B.wittLift_residue w

/-- The residue characteristic lies in the maximal ideal. -/
theorem p_mem_maximalIdeal : (p : B.R) ∈ IsLocalRing.maximalIdeal B.R := by
  rw [← B.reduction_eq_zero_iff, map_natCast, CharP.cast_eq_zero]

/-- The unramified coefficient field embeds in the generic coefficient field. -/
def coefficientInclusion : B.K₀ →+* B.K :=
  IsFractionRing.lift (g := (algebraMap B.R B.K).comp B.wittLift)
    ((IsFractionRing.injective B.R B.K).comp B.wittLift_injective)

/-- Scalar extension from the unramified coefficient field. -/
instance coefficientAlgebra : Algebra B.K₀ B.K := B.coefficientInclusion.toAlgebra

@[simp]
theorem coefficientInclusion_algebraMap (w : WittVector p B.k) :
    B.coefficientInclusion (algebraMap (WittVector p B.k) B.K₀ w) =
      algebraMap B.R B.K (B.wittLift w) :=
  IsFractionRing.lift_algebraMap _ w

/-- The generic fibre, defined by actual scheme base change. -/
def genericFiber (X : Over (Spec (CommRingCat.of B.R))) :
    Over (Spec (CommRingCat.of B.K)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.K)))).obj X

/-- The special fibre, defined by actual scheme base change. -/
def specialFiber (X : Over (Spec (CommRingCat.of B.R))) :
    Over (Spec (CommRingCat.of B.k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom B.reduction))).obj X

instance genericFiber_smooth (X : Over (Spec (CommRingCat.of B.R))) [Smooth X.hom] :
    Smooth (B.genericFiber X).hom := by
  dsimp [MixedCharacteristicDVR.genericFiber]
  infer_instance

instance genericFiber_proper (X : Over (Spec (CommRingCat.of B.R))) [IsProper X.hom] :
    IsProper (B.genericFiber X).hom := by
  dsimp [MixedCharacteristicDVR.genericFiber]
  infer_instance

instance specialFiber_smooth (X : Over (Spec (CommRingCat.of B.R))) [Smooth X.hom] :
    Smooth (B.specialFiber X).hom := by
  dsimp [MixedCharacteristicDVR.specialFiber]
  infer_instance

instance specialFiber_proper (X : Over (Spec (CommRingCat.of B.R))) [IsProper X.hom] :
    IsProper (B.specialFiber X).hom := by
  dsimp [MixedCharacteristicDVR.specialFiber]
  infer_instance

/-- The actual smooth model supplies finite polynomial frames for every native crystalline chart. -/
theorem exists_finite_crystalline_frame (X : Over (Spec (CommRingCat.of B.R))) [Smooth X.hom]
    (Q : Site.Object p B.k (B.specialFiber X)) :
    ∃ n : ℕ, ∃ g : Q ⟶ Finite.WittFrames.CrystallineSmoothCharts.frame p B.k (B.specialFiber X) Q n,
      g.reducedMap = AlgHom.id B.k Q.residueRing :=
  Finite.WittFrames.CrystallineSmoothCharts.exists_frameMap p B.k (B.specialFiber X) Q

/-- Frobenius on the coefficient field; no extension to the possibly
ramified field `B.K` is chosen. -/
def coefficientFrobenius : B.K₀ ≃+* B.K₀ :=
  WittVector.FractionRing.frobenius p B.k

end MixedCharacteristicDVR

/-- Rational crystalline cohomology of the actual special fibre. -/
def rationalCrystalline {p : ℕ} [Fact p.Prime] (B : MixedCharacteristicDVR.{u} p)
    (X : Over (Spec (CommRingCat.of B.R))) (n : ℕ) : ModuleCat.{u + 2} B.K₀ :=
  Site.rationalCohomology p B.k (B.specialFiber X) n

/-- Algebraic de Rham hypercohomology of the actual generic fibre, using
the explicit differential-form presentation. -/
def algebraicDeRham {p : ℕ} [Fact p.Prime] (B : MixedCharacteristicDVR.{u} p)
    (X : Over (Spec (CommRingCat.of B.R))) (n : ℕ) : ModuleCat.{u + 1} B.K :=
  DeRhamGlobalId.DeRhamGlobal.cohomology B.K (B.genericFiber X) n

/-- The original generic-fiber de Rham cohomology is finite-dimensional. -/
theorem algebraicDeRham_finite {p : ℕ} [Fact p.Prime] (B : MixedCharacteristicDVR.{u} p)
    (X : Over (Spec (CommRingCat.of B.R))) [Smooth X.hom] [IsProper X.hom] (n : ℕ) :
    FiniteDimensional B.K (algebraicDeRham B X n) :=
  SmoothProperTermFinite.SmoothProperDeRhamFiniteness.finite B.K (B.genericFiber X) n

/-- The Hodge filtration obtained from degree truncation of the generic-fibre
de Rham complex. -/
def hodgeFiltration {p : ℕ} [Fact p.Prime] (B : MixedCharacteristicDVR.{u} p)
    (X : Over (Spec (CommRingCat.of B.R))) (n : ℕ) (j : ℤ) :
    Submodule B.K (algebraicDeRham B X n) :=
  HodgeFiltrationD.HodgeFiltration.filtration B.K (B.genericFiber X) n j

theorem hodgeFiltration_antitone {p : ℕ} [Fact p.Prime] (B : MixedCharacteristicDVR.{u} p)
    (X : Over (Spec (CommRingCat.of B.R))) (n : ℕ) : Antitone (hodgeFiltration B X n) :=
  HodgeFiltrationD.HodgeFiltration.filtration_antitone B.K (B.genericFiber X) n

variable {K : Type*} [Field K]
  {C D : Type*} [AddCommGroup C] [Module K C]
  [AddCommGroup D] [Module K D]

/-- Pulling back a decreasing filtration preserves its order condition. -/
theorem transportedFiltration_antitone
    (f : C →ₗ[K] D) (F : ℤ → Submodule K D) (hF : Antitone F) :
    Antitone (fun j => (F j).comap f) := by
  intro i j hij
  exact Submodule.comap_mono (hF hij)

/-- The transported filtration maps back to the original filtration. -/
theorem transportedFiltration_map
    (e : C ≃ₗ[K] D) (F : ℤ → Submodule K D) (j : ℤ) :
    ((F j).comap e.toLinearMap).map e.toLinearMap = F j := by
  exact Submodule.map_comap_eq_of_surjective e.surjective (F j)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Foundations
