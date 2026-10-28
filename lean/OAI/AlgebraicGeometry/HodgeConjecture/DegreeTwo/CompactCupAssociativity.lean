import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCohomologyCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupAssociativity

/-! # Compact Cup Associativity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupAssociativity.Constructions

noncomputable section

/-! Associativity of the actual compact-support cup action, with exact degree transport. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0})

theorem compactCohomologyι_degreeCast (K : Compacts X) {p q : ℕ} (h : p=q)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) h)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K p a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K q
      (eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ) h) a) := by
  subst q
  rfl

theorem compactCohomologyRightCup_assoc (p q r : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X r) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) (Nat.add_assoc p q r))
      (CompactCohomologyCup.Constructions.compactCohomologyRightCup X (p+q) r c (CompactCohomologyCup.Constructions.compactCohomologyRightCup X p q b a)) =
    CompactCohomologyCup.Constructions.compactCohomologyRightCup X p (q+r) (AlgebraicTopology.Products.CupCohomology.cohomologyCup (R := ℚ) (TopCat.toSSet.obj X) q r b c) a := by
  obtain ⟨K,a,rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ) X p a
  rw [CompactCohomologyCup.Constructions.compactCohomologyRightCup_stage, CompactCohomologyCup.Constructions.compactCohomologyRightCup_stage,
    compactCohomologyι_degreeCast X K (Nat.add_assoc p q r), CompactCohomologyCup.Constructions.compactCohomologyRightCup_stage]
  apply congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K (p+(q+r)))
  rw [← RelativeCupAssociativity.Constructions.relativeCohomologyCast_eqToHom X (K : Set X)ᶜ (Nat.add_assoc p q r)]
  exact RelativeCupAssociativity.Constructions.relativeAbsoluteCohomologyCup_assoc X (K : Set X)ᶜ a b c

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupAssociativity.Constructions
