import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupAssociativity
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupTrace

/-! # Compact Cup Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupEvaluation.Constructions

noncomputable section

/-! Actual compact cup products can be moved across the native evaluation pairing. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem compactCohomologyDegreeCast_trans (X : TopCat.{0}) {p q r : ℕ}
    (h : p=q) (h' : q=r) (h'' : p=r)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p) :
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) h')
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) h) a) =
    eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X) h'') a := by
  subst q r
  rfl

theorem compactSupportEvaluation_rightCup (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    (p q r : ℕ) (h : p+(q+r)=2*d)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) r) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d r (p+q) (by omega) c
      (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of M) p q b a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (q+r) p (by omega)
      (AlgebraicTopology.Products.CupCohomology.cohomologyCup (R := ℚ) (TopCat.toSSet.obj (TopCat.of M)) q r b c) a := by
  have hL := CompactCupTrace.Constructions.compactCohomologyRightCup_trace d (p+q) r (by omega) c
    (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of M) p q b a)
  have hR := CompactCupTrace.Constructions.compactCohomologyRightCup_trace d p (q+r) h
    (AlgebraicTopology.Products.CupCohomology.cohomologyCup (R := ℚ) (TopCat.toSSet.obj (TopCat.of M)) q r b c) a
  have ha := congrArg
    (fun z => AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)) h) z))
    (CompactCupAssociativity.Constructions.compactCohomologyRightCup_assoc (TopCat.of M) p q r a b c)
  have hd := congrArg (AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M))
    (compactCohomologyDegreeCast_trans (TopCat.of M) (Nat.add_assoc p q r) h (by omega)
      (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of M) (p+q) r c
        (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of M) p q b a)))
  exact hL.symm.trans (hd.symm.trans (ha.trans hR))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupEvaluation.Constructions
