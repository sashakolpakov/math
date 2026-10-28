import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

/-! # Compact Cohomology Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCohomologyCup.Constructions

noncomputable section

/-! Actual compact-support cup with an ordinary class, descended from the relative cup. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (p q : ℕ)
variable (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)

def compactCohomologyRightCupStage (K : Compacts X) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X (p+q) :=
  ModuleCat.ofHom ((CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X (K : Set X)ᶜ p q).flip a) ≫
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K (p+q)

theorem compactCohomologyRightCupStage_naturality {K L : Compacts X} (h : K ≤ L) :
    AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h p ≫ compactCohomologyRightCupStage X p q a L =
      compactCohomologyRightCupStage X p q a K := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  have hc := CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_supportEnlargement (R := ℚ) X (K : Set X)ᶜ
    (Set.compl_subset_compl.mpr h) p q b a
  have he := ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_ι (ModuleCat.of ℚ ℚ) h (p+q))
    (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X (K : Set X)ᶜ p q b a)
  exact (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X L (p+q)) hc.symm).trans he

def compactCohomologyRightCup :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X (p+q) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) X p
    (compactCohomologyRightCupStage X p q a)
    (fun _ _ h => compactCohomologyRightCupStage_naturality X p q a h)

theorem compactCohomologyRightCup_stage (K : Compacts X)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p) :
    compactCohomologyRightCup X p q a
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K p b) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K (p+q)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X (K : Set X)ᶜ p q b a) :=
  ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyι_desc (ModuleCat.of ℚ ℚ) X p
    (compactCohomologyRightCupStage X p q a)
    (fun _ _ h => compactCohomologyRightCupStage_naturality X p q a h) K) b

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCohomologyCup.Constructions
