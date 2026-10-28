import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.RepresentableOpenGlueData
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Subterminal Relative Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalRelativeChart

noncomputable section

/-! An open base chart pulls back to every test scheme. Maps into a monomorphism over that chart determine compatible lifts to this pullback. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem overHom_subsingleton_of_mono_structure {S : Scheme.{u}} (M : Over S) [Mono M.hom]
    (T : Over S) : Subsingleton (T ⟶ M) := by
  constructor
  intro a b
  apply Over.OverMorphism.ext
  exact (cancel_mono M.hom).mp (a.w.trans b.w.symm)

variable {S U : Scheme.{u}} (i : U ⟶ S) (T : Over S)

def baseChartTest : Over S := (Over.map i).obj ((Over.pullback i).obj T)

def baseChartProjection : baseChartTest i T ⟶ T :=
  Over.homMk (pullback.fst T.hom i) (pullback.condition (f := T.hom) (g := i))

theorem baseChartProjection_open [IsOpenImmersion i] : IsOpenImmersion (baseChartProjection i T).left :=
  inferInstanceAs (IsOpenImmersion (pullback.fst T.hom i))

theorem baseChartProjection_mono [IsOpenImmersion i] : Mono (baseChartProjection i T) := by
  have : IsOpenImmersion (baseChartProjection i T).left := baseChartProjection_open i T
  exact Over.mono_of_mono_left _

def baseChartTestLift (M : Over U) {V : Over S}
    (a : V ⟶ (Over.map i).obj M) (b : V ⟶ T) : V ⟶ baseChartTest i T := by
  have h : b.left ≫ T.hom = (a.left ≫ M.hom) ≫ i :=
    b.w.trans ((Category.assoc a.left M.hom i).trans a.w).symm
  let l := pullback.lift b.left (a.left ≫ M.hom) h
  exact Over.homMk l ((Category.assoc l (pullback.snd T.hom i) i).symm.trans
    ((congrArg (fun z => z ≫ i) (pullback.lift_snd b.left (a.left ≫ M.hom) h)).trans
      ((Category.assoc a.left M.hom i).trans a.w)))

theorem baseChartTestLift_projection (M : Over U) {V : Over S}
    (a : V ⟶ (Over.map i).obj M) (b : V ⟶ T) :
    baseChartTestLift i T M a b ≫ baseChartProjection i T = b := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

theorem baseChartTestLift_toChart (M : Over U) [Mono i] [Mono M.hom] {V : Over S}
    (a : V ⟶ (Over.map i).obj M) (b : V ⟶ T) (m : baseChartTest i T ⟶ (Over.map i).obj M) :
    baseChartTestLift i T M a b ≫ m = a := by
  have : Mono ((Over.map i).obj M).hom := inferInstanceAs (Mono (M.hom ≫ i))
  have : Subsingleton (V ⟶ (Over.map i).obj M) := overHom_subsingleton_of_mono_structure _ _
  exact Subsingleton.elim _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalRelativeChart
