import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingResidue
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingPullback
import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

/-! # Normal Residue -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalResidue

noncomputable section

/-!
# DegreeTwo: logarithmic residues in genuine normal coordinates

Naturality of both the actual winding class and the actual relative connecting
map identifies the local logarithmic residue with pullback of the nonzero
universal normal generator. For an actual normal chart this is a generator of
its genuine relative singular cohomology group.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

namespace Constructions.ExponentialCocycle

variable {X : TopCat.{0}} (g : X ⟶ ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane) (A : Set X)
  (hA : Set.MapsTo g A ({0}ᶜ : Set ℂ))

/-- The actual restriction of a complex-valued map to a subspace where it is nonzero. -/
def nonzeroRestriction : TopCat.of A ⟶ ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured := CycleClass.Geometric.LocalHomology.Cycles.subspaceMap g hA

def restrictedFunction : C(TopCat.of A, ℂ) :=
  WindingNormalization.Constructions.ExponentialCocycle.tautologicalFunction.comp (nonzeroRestriction g A hA).hom

/-- Restriction of the coordinate function pulls back the actual universal winding class. -/
theorem restrictedFunction_winding :
    DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass (TopCat.of A) (restrictedFunction g A hA)
        (fun x => (nonzeroRestriction g A hA x).property) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (nonzeroRestriction g A hA) 1 WindingNormalization.Constructions.ExponentialCocycle.universalWindingClass :=
  WindingPullback.Constructions.CechPullback.logarithmicWindingClass_pullback (nonzeroRestriction g A hA)
    WindingNormalization.Constructions.ExponentialCocycle.tautologicalFunction (fun z => z.property)

/-- The connecting class of the actual restricted function is the actual pair
 pullback of the universal logarithmic residue. -/
theorem restrictedFunction_residue :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting ExponentialCocycleQ.Constructions.ExponentialCocycle.Q X A 1
      (DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass (TopCat.of A) (restrictedFunction g A hA)
        (fun x => (nonzeroRestriction g A hA x).property)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q g hA 2 WindingResidue.Constructions.ExponentialCocycle.windingResidueClass := by
  rw [restrictedFunction_winding]
  exact (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_naturality ExponentialCocycleQ.Constructions.ExponentialCocycle.Q g hA 1)
    WindingNormalization.Constructions.ExponentialCocycle.universalWindingClass).symm

/-- Its scalar relative to the fixed normal model is the same proved nonzero
 rational number for every actual map of pairs. -/
theorem restrictedFunction_residue_eq_smul :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting ExponentialCocycleQ.Constructions.ExponentialCocycle.Q X A 1
      (DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass (TopCat.of A) (restrictedFunction g A hA)
        (fun x => (nonzeroRestriction g A hA x).property)) =
    WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q g hA 2 WindingResidue.Constructions.ExponentialCocycle.planeNormalClass := by
  rw [restrictedFunction_residue, WindingResidue.Constructions.ExponentialCocycle.windingResidueClass_eq_smul_normal, map_smul]

end Constructions.ExponentialCocycle

namespace Constructions

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E ℂ f x)

/-- The local residue defined by the actual normal coordinate on the actual complement. -/
def normalLogarithmicResidue : P.relativeCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.of P.neighborhood) P.relativeComplement 1
    (DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass (TopCat.of P.relativeComplement)
      (ExponentialCocycle.restrictedFunction P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo)
      (fun y => (ExponentialCocycle.nonzeroRestriction P.normalCoordinate P.relativeComplement
        P.normalCoordinate_mapsTo y).property))

theorem normalLogarithmicResidue_eq_pullback :
    normalLogarithmicResidue P = P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2 WindingResidue.Constructions.ExponentialCocycle.windingResidueClass :=
  ExponentialCocycle.restrictedFunction_residue P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo

theorem normalLogarithmicResidue_eq_smul :
    normalLogarithmicResidue P =
      WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient • P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2 WindingResidue.Constructions.ExponentialCocycle.planeNormalClass := by
  rw [normalLogarithmicResidue_eq_pullback, WindingResidue.Constructions.ExponentialCocycle.windingResidueClass_eq_smul_normal, map_smul]

variable [NormedSpace ℝ E]

/-- In an actual normal chart the logarithmic residue is nonzero. -/
theorem normalLogarithmicResidue_ne_zero : normalLogarithmicResidue P ≠ 0 := by
  intro hz
  apply WindingResidue.Constructions.ExponentialCocycle.windingResidueClass_ne_zero
  apply (P.relativeCohomologyIso 2).toLinearEquiv.injective
  change (P.relativeCohomologyIso 2).hom WindingResidue.Constructions.ExponentialCocycle.windingResidueClass = (P.relativeCohomologyIso 2).hom 0
  rw [map_zero, P.relativeCohomologyIso_hom, ← normalLogarithmicResidue_eq_pullback]
  exact hz

/-- The local logarithmic residue generates the genuine relative group of the normal chart. -/
theorem normalLogarithmicResidue_generates (a : P.relativeCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2) :
    ∃ q : ℚ, q • normalLogarithmicResidue P = a := by
  obtain ⟨q, hq⟩ := WindingResidue.Constructions.ExponentialCocycle.windingResidueClass_generates ((P.relativeCohomologyIso 2).inv a)
  refine ⟨q, ?_⟩
  rw [normalLogarithmicResidue_eq_pullback, ← map_smul, hq,
    ← P.relativeCohomologyIso_hom, Iso.inv_hom_id_apply]

end Constructions

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalResidue
