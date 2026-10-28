import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech

/-! # Winding Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingPullback.Constructions.CechPullback

noncomputable section

/-! Actual continuous pullback of the logarithm-branch winding class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech.RationalCech

variable {X Y : TopCat.{0}} {I : Type} (f : Y ⟶ X) (U : I → Opens X)

def branchPullback (b : DivisorClass.Chern.WindingCech.RationalCech.BranchCochain X U) : DivisorClass.Chern.WindingCech.RationalCech.BranchCochain Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) :=
  fun a => (b a).comp (CechPullbackF.Constructions.CechPullback.intersectionMap f U a).hom

theorem branchDelta_pullback (b : DivisorClass.Chern.WindingCech.RationalCech.BranchCochain X U)
    (a : Fin 2 → I) (y : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechPullbackF.Constructions.CechPullback.pulledCover f U) a) :
    DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (DivisorClass.Chern.LogCech.RationalCech.continuousComplexPresheaf Y) (CechPullbackF.Constructions.CechPullback.pulledCover f U) 0 (branchPullback f U b) a y =
      DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (DivisorClass.Chern.LogCech.RationalCech.continuousComplexPresheaf X) U 0 b a (CechPullbackF.Constructions.CechPullback.intersectionMap f U a y) := by
  rw [DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta_apply, DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  rfl

theorem branchCompatibility_pullback (b : DivisorClass.Chern.WindingCech.RationalCech.BranchCochain X U) (h : DivisorClass.Chern.WindingCech.RationalCech.BranchCompatibility X U b) :
    DivisorClass.Chern.WindingCech.RationalCech.BranchCompatibility Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) (branchPullback f U b) := by
  intro a y
  rw [branchDelta_pullback]
  exact h a (CechPullbackF.Constructions.CechPullback.intersectionMap f U a y)

theorem branchWindingCocycle_pullback (b : DivisorClass.Chern.WindingCech.RationalCech.BranchCochain X U) (h : DivisorClass.Chern.WindingCech.RationalCech.BranchCompatibility X U b) :
    DivisorClass.Chern.WindingCech.RationalCech.branchWindingCocycle Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) (branchPullback f U b)
      (branchCompatibility_pullback f U b h) =
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CechPullbackF.Constructions.CechPullback.locallyConstantCochainMap f U) 1 (DivisorClass.Chern.WindingCech.RationalCech.branchWindingCocycle X U b h) := by
  apply Subtype.ext
  funext a
  apply LocallyConstant.ext
  intro y
  change (DivisorClass.Chern.Logarithms.Construction.logarithmicDefect
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (DivisorClass.Chern.LogCech.RationalCech.continuousComplexPresheaf Y) (CechPullbackF.Constructions.CechPullback.pulledCover f U) 0 (branchPullback f U b) a y)
      0 0 _ : ℚ) =
    (DivisorClass.Chern.Logarithms.Construction.logarithmicDefect
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (DivisorClass.Chern.LogCech.RationalCech.continuousComplexPresheaf X) U 0 b a (CechPullbackF.Constructions.CechPullback.intersectionMap f U a y)) 0 0 _ : ℚ)
  have hcongr (z w : ℂ) (he : z = w)
      (hz : Complex.exp z * Complex.exp 0 = Complex.exp 0)
      (hw : Complex.exp w * Complex.exp 0 = Complex.exp 0) :
      DivisorClass.Chern.Logarithms.Construction.logarithmicDefect z 0 0 hz =
        DivisorClass.Chern.Logarithms.Construction.logarithmicDefect w 0 0 hw := by
    cases he
    rfl
  exact congrArg (fun n : ℤ => (n : ℚ))
    (hcongr _ _ (branchDelta_pullback f U b a y) _ _)

theorem branchWindingClass_pullback (hU : ∀ x : X, ∃ i, x ∈ U i)
    (b : DivisorClass.Chern.WindingCech.RationalCech.BranchCochain X U) (h : DivisorClass.Chern.WindingCech.RationalCech.BranchCompatibility X U b) :
    DivisorClass.Chern.WindingCech.RationalCech.branchWindingClass Y (CechPullbackF.Constructions.CechPullback.pulledCover f U) (CechPullbackF.Constructions.CechPullback.pulledCover_covers f U hU)
      (branchPullback f U b) (branchCompatibility_pullback f U b h) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 (DivisorClass.Chern.WindingCech.RationalCech.branchWindingClass X U hU b h) := by
  unfold DivisorClass.Chern.WindingCech.RationalCech.branchWindingClass
  rw [branchWindingCocycle_pullback]
  exact CechPullbackF.Constructions.CechPullback.classOfCechCocycle_naturality f U hU 1 (DivisorClass.Chern.WindingCech.RationalCech.branchWindingCocycle X U b h)

/-- The canonical winding class commutes with actual singular-cohomology pullback. -/
theorem logarithmicWindingClass_pullback (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0) :
    DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass Y (g.comp f.hom) (fun y => hg (f y)) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 (DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass X g hg) := by
  let U := DivisorClass.Chern.WindingCech.RationalCech.functionLogCover X g
  let b := DivisorClass.Chern.WindingCech.RationalCech.functionLogBranches X g
  have hU := DivisorClass.Chern.WindingCech.RationalCech.functionLogCover_covers X g hg
  have hb := DivisorClass.Chern.WindingCech.RationalCech.functionLogBranches_compatible X g hg
  rw [← DivisorClass.Chern.WindingCech.RationalCech.branchWindingClass_eq_logarithmicWindingClass Y (CechPullbackF.Constructions.CechPullback.pulledCover f U)
    (CechPullbackF.Constructions.CechPullback.pulledCover_covers f U hU) (g.comp f.hom) (fun y => hg (f y))
    (branchPullback f U b) (branchCompatibility_pullback f U b hb)
    (fun a y => DivisorClass.Chern.WindingCech.RationalCech.functionLogBranches_exp X g hg a (CechPullbackF.Constructions.CechPullback.intersectionMap f U a y))]
  exact branchWindingClass_pullback f U hU b hb

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingPullback.Constructions.CechPullback
