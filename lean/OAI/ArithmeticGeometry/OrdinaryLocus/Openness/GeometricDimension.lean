import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseChange

/-! # Geometric Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricDimension.Construction

noncomputable section

/-! Relating the geometric dimension to the residue-field fiber in Openness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- An algebraic extension of the base field preserves scheme dimension. -/
theorem topologicalKrullDim_algebraic_baseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    topologicalKrullDim (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let σ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : IsIntegralHom σ := IsIntegralHom.SpecMap_iff.mpr
    (Algebra.IsIntegral.isIntegral : (algebraMap K L).IsIntegral)
  have : Surjective σ := ⟨fun x =>
    ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact IntegralDimension.Construction.topologicalKrullDim_eq_of_integral_surjective (pullback.fst f σ)

/-- The dimension in Openness can be computed on its geometric fiber. -/
theorem topologicalKrullDim_geometricFiber
    {S : Scheme} (A : Over S) (s : S) :
    topologicalKrullDim (DefinitionsTorsion.Construction.geometricFiberScheme A s) =
      topologicalKrullDim (A.hom.fiber s) := by
  let σ := Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s))))
  let e := pullbackLeftPullbackSndIso A.hom (S.fromSpecResidueField s) σ
  have hdim := topologicalKrullDim_algebraic_baseChange
    (K := S.residueField s) (L := AlgebraicClosure (S.residueField s))
    (A.hom.fiberToSpecResidueField s)
  change topologicalKrullDim (pullback (pullback.snd A.hom (S.fromSpecResidueField s)) σ : Scheme) =
    topologicalKrullDim (A.hom.fiber s) at hdim
  have he := e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  exact he.symm.trans hdim

/-- Every fiber of a smooth proper geometrically connected commutative
group has finite natural-number dimension, with the exact Openness convention. -/
theorem exists_nat_dimension_fiber_group
    {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] (s : S) :
    ∃ g : ℕ, topologicalKrullDim (A.hom.fiber s) = (g : WithBot ℕ∞) := by
  let t : Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
    (DefinitionsTorsion.geometricPoint S s).hom
  let F := Over.pullback t
  let B := F.obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (DefinitionsTorsion.Construction.geometricFiberMap A s))
  have : IsProper B.hom := inferInstanceAs (IsProper (DefinitionsTorsion.Construction.geometricFiberMap A s))
  have : GeometricallyConnected B.hom :=
    inferInstanceAs (GeometricallyConnected (DefinitionsTorsion.Construction.geometricFiberMap A s))
  obtain ⟨g, hg⟩ := GroupDimension.Construction.exists_nat_dimension_group_over_algClosed B
  refine ⟨g, (topologicalKrullDim_geometricFiber A s).symm.trans hg⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricDimension.Construction
