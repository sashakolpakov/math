import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateChoices
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints

/-! # Active Choices -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ActiveChoices

noncomputable section

/-! The original geometric active subgroup-choice functor is
exhaustively classified by subspaces of its actual q-torsion points.
Membership retains the original inclusion into the abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices

variable {S : Scheme} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable (q : ℕ) [Fact q.Prime] (m : ℕ) [hm : Fact (1 ≤ m)] (i : Fin 3)
variable (K : Type) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)
variable (p : A ⟶ A) [IsMonHom p]
variable [IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p).hom] [Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p).hom]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance activeModuleAtLevel :
    Module (ZMod (q ^ m)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q m (HeckeExponents.activeExponents i)
    (fun k => (HeckeExponents.activeExponents_bound i k).trans hm.out)

abbrev geometricBlockPointGroup := Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p)

instance geometricBlockPointGroup_finite : Finite (geometricBlockPointGroup q m K b p) :=
  Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_overPoints (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p) b

def geometricActiveChoiceEquiv :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ m) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) p (Over.mk b) ≃
      {L : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q (geometricBlockPointGroup q m K b p)) //
        Module.finrank (ZMod q) L = HeckeExponents.neighborLevel i} :=
  (AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv (q ^ m) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i))
    K b p (AddEquiv.refl (geometricBlockPointGroup q m K b p))).trans
      (ActiveTorsionChoices.activeTorsionSubspaceEquiv q (geometricBlockPointGroup q m K b p) i)

theorem geometricActiveChoiceEquiv_membership
    (F : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ m) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) p (Over.mk b))
    (x : ActiveTorsionChoices.killedSubgroup q (geometricBlockPointGroup q m K b p)) :
    x ∈ (geometricActiveChoiceEquiv q m i K b p F).val ↔
      x.val.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p ∈ F.val.subgroup.points (Over.mk b) (𝟙 _) :=
  (ActiveTorsionChoices.activeTorsionSubspaceEquiv_membership q (geometricBlockPointGroup q m K b p) i
    (AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv (q ^ m) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i))
      K b p (AddEquiv.refl _) F) x).trans
        (AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv_membership (q ^ m)
          (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) K b p (AddEquiv.refl _) F x.val)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ActiveChoices
