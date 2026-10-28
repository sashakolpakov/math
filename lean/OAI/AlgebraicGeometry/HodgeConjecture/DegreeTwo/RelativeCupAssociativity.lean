import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

/-! # Relative Cup Associativity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupAssociativity.Constructions

noncomputable section

/-! Associativity retains the actual relative support in the left cup factor. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A : Set X)

theorem relativeAbsoluteCup_assoc {p q r : ℕ}
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X r) :
    CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of ℚ ℚ) X A (Nat.add_assoc p q r)
      (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X A (p+q) r (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X A p q a b) c) =
    CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X A p (q+r) a (AlgebraicTopology.Products.Cup.singularCup X b c) := by
  apply CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of ℚ ℚ) X A (p+(q+r))
  simp only [CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast_inclusion, CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup, CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion]
  exact AlgebraicTopology.Products.Cup.cup_assoc (TopCat.toSSet.obj X)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a) b c

theorem relativeAbsoluteCohomologyCup_assoc {p q r : ℕ}
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X r) :
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) X A (Nat.add_assoc p q r)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X A (p+q) r
        (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X A p q a b) c) =
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X A p (q+r) a
      (AlgebraicTopology.Products.CupCohomology.cohomologyCup (R := ℚ) (TopCat.toSSet.obj X) q r b c) := by
  obtain ⟨a,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a
  obtain ⟨b,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q b
  obtain ⟨c,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) r c
  rw [CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class, CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class,
    AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class, CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class, CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) (p+(q+r)))
  apply Subtype.ext
  rw [CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCocycleCast_val]
  exact relativeAbsoluteCup_assoc X A a.val b.val c.val

theorem relativeCohomologyCast_eqToHom {p q : ℕ} (h : p=q)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p) :
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) X A h a =
      eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A) h) a := by
  subst q
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupAssociativity.Constructions
