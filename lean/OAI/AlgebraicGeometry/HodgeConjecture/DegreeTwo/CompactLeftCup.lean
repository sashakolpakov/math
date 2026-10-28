import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCohomologyCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupAssociativity
import OAI.AlgebraicTopology.Products.RelativeCupGradedCommutativity

/-! # Compact Left Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions

noncomputable section

/-! Actual ordinary-left cup multiplication on compact-support cohomology. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Products.RelativeCupGradedCommutativity

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (p q : ℕ) (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)

def compactCohomologyLeftCupStage (K : Compacts X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ q ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X (p+q) :=
  ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X (K : Set X)ᶜ p q a) ≫
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K (p+q)

theorem compactCohomologyLeftCupStage_naturality {K L : Compacts X} (h : K ≤ L) :
    AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h q ≫ compactCohomologyLeftCupStage X p q a L =
      compactCohomologyLeftCupStage X p q a K := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  have hc := CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup_supportEnlargement (R := ℚ) X (K : Set X)ᶜ
    (Set.compl_subset_compl.mpr h) p q a b
  have he := ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_ι (ModuleCat.of ℚ ℚ) h (p+q))
    (CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X (K : Set X)ᶜ p q a b)
  exact (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X L (p+q)) hc.symm).trans he

def compactCohomologyLeftCup :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X q ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X (p+q) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) X q
    (compactCohomologyLeftCupStage X p q a)
    (fun _ _ h => compactCohomologyLeftCupStage_naturality X p q a h)

theorem compactCohomologyLeftCup_stage (K : Compacts X)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ q) :
    compactCohomologyLeftCup X p q a
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K q b) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K (p+q)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X (K : Set X)ᶜ p q a b) :=
  ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyι_desc (ModuleCat.of ℚ ℚ) X q
    (compactCohomologyLeftCupStage X p q a)
    (fun _ _ h => compactCohomologyLeftCupStage_naturality X p q a h) K) b

theorem compactCohomologyLeftCup_graded_comm
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X q) :
    compactCohomologyLeftCup X p q a b = (-1 : ℚ)^(p*q) •
      eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) (Nat.add_comm q p))
        (CompactCohomologyCup.Constructions.compactCohomologyRightCup X q p a b) := by
  obtain ⟨K,b,rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ) X q b
  rw [compactCohomologyLeftCup_stage, AlgebraicTopology.Products.RelativeCupGradedCommutativity.absoluteRelativeCohomologyCup_graded_comm,
    map_smul, CompactCohomologyCup.Constructions.compactCohomologyRightCup_stage,
    CompactCupAssociativity.Constructions.compactCohomologyι_degreeCast X K (Nat.add_comm q p),
    RelativeCupAssociativity.Constructions.relativeCohomologyCast_eqToHom]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions
