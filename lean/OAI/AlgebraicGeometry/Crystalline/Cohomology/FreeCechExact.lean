import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechEvaluation

/-! # Free Cech Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechExact.CrystallineFreeCechExact

noncomputable section

/-!
# Positive exactness of native free Čech sheaves

At each native test object the free Čech chain complex is isomorphic to
the contracted fibrewise tuple complex. Evaluation detects zero homology
presheaves, and exact native sheafification preserves this exactness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring) (M : SheafInjectives.CrystallineSheafInjectives.Modules p k)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

theorem evaluated_exactAt (T : Site.Object p k X) (n : ℕ) (hn : n ≠ 0) :
    ((((CategoryTheory.evaluation _ V).obj (op T)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (FreeCech.CrystallineFreeCech.complex p k X Q s M)).ExactAt n :=
  (FiberTuple.FiberTupleCech.exactAt (CrystallineCech.ArrowTuples.CrystallineCechArrowTuples.LiftIndex p k X Q T s) V M n hn).of_iso
    (FreeCechEvaluation.CrystallineFreeCechEvaluation.chainIso p k X Q T s M).symm

theorem presheaf_exactAt (n : ℕ) (hn : n ≠ 0) :
    (FreeCech.CrystallineFreeCech.complex p k X Q s M).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply Functor.isZero
  intro T
  have hz := (evaluated_exactAt p k X Q s M T.unop n hn).isZero_homology
  exact hz.of_iso
    (((FreeCech.CrystallineFreeCech.complex p k X Q s M).sc n).mapHomologyIso
      ((CategoryTheory.evaluation _ V).obj T)).symm

theorem sheaf_exactAt (n : ℕ) (hn : n ≠ 0) :
    (FreeCech.CrystallineFreeCech.sheafComplex p k X Q s M).ExactAt n :=
  (presheaf_exactAt p k X Q s M n hn).map (presheafToSheaf J V)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechExact.CrystallineFreeCechExact
