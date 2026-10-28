import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex

/-! # PD Lift Independence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDLiftIndependence.Complex

noncomputable section

/-! Changing lifts of the same residual parameters leaves the actual
supported Čech–PD residue class unchanged. The comparison is made in
the original supported total built from the original parameter opens. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open _root_.Complex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X)
  (g : ℕ) (a b : Fin g → Q.thickening.ring)
  (hab : ∀ i, Q.thickening.reduction (b i) = Q.thickening.reduction (a i))

def changedCoordinate (i : Fin g) : (PDComplex.topFrame p k X Q g a).thickening.ring :=
  (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (PDComplex.topCoefficient p k X Q g a)).ambientMap (b i)

include hab in
theorem coordinate_difference (i : Fin g) :
    changedCoordinate p k X Q g a b i - PDComplex.coordinate p k X Q g a i ∈
      RingHom.ker (PDComplex.topFrame p k X Q g a).thickening.reduction := by
  change (PDComplex.topFrame p k X Q g a).thickening.reduction
    (changedCoordinate p k X Q g a b i - PDComplex.coordinate p k X Q g a i) = 0
  rw [map_sub]
  apply sub_eq_zero.mpr
  let f := AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (PDComplex.topCoefficient p k X Q g a)
  exact (f.reduction_comm (b i)).trans
    ((congrArg f.reducedMap (hab i)).trans (f.reduction_comm (a i)).symm)

include hab in
theorem changedCoordinate_isUnit (i : Fin g) : IsUnit (changedCoordinate p k X Q g a b i) := by
  have hn := DividedPower.Nilpotence.nilpotent_of_mem
    (PDComplex.topFrame p k X Q g a).thickening.dividedPowers p (Fact.out : p.Prime).pos
    (PDComplex.topFrame p k X Q g a).thickening.p_nilpotent (coordinate_difference p k X Q g a b hab i)
  have h := hn.isUnit_add_right_of_commute (PDComplex.coordinate_isUnit p k X Q g a i) (Commute.all _ _)
  simpa only [sub_add_cancel] using h

def changedCoordinateUnit (i : Fin g) : (PDComplex.topFrame p k X Q g a).thickening.ringˣ :=
  (changedCoordinate_isUnit p k X Q g a b hab i).unit

theorem changedCoordinateUnit_val (i : Fin g) :
    (changedCoordinateUnit p k X Q g a b hab i : (PDComplex.topFrame p k X Q g a).thickening.ring) =
      changedCoordinate p k X Q g a b i :=
  (changedCoordinate_isUnit p k X Q g a b hab i).unit_spec

def changedLogarithmicForm : ((PDComplex.localizedComplex p k X Q).X g).obj (op (PDComplex.topCoefficient p k X Q g a)) :=
  PD.LogarithmicWedges.Forms.logarithmicWedge (WittVector p k) (PDComplex.topFrame p k X Q g a).thickening.ring
    (RingHom.ker (PDComplex.topFrame p k X Q g a).thickening.reduction)
    (PDComplex.topFrame p k X Q g a).thickening.dividedPowers g (changedCoordinateUnit p k X Q g a b hab)

theorem changedLogarithmicForm_closed :
    ((PDComplex.localizedComplex p k X Q).d g (g + 1)).app (op (PDComplex.topCoefficient p k X Q g a))
      (changedLogarithmicForm p k X Q g a b hab) = 0 := by
  rw [PDComplex.localizedComplex_d]
  exact PD.LogarithmicWedges.Forms.logarithmicWedge_closed _ _ _ _ g _

def changedResidueClass : (PDComplex.total p k X Q g a).homology (g + g) :=
  AugmentedOrdered.CechTopTotal.topTotalClass (PDComplex.family p k X Q g a) (PDComplex.localizedComplex p k X Q)
    g (by simp) g (changedLogarithmicForm p k X Q g a b hab)
    (changedLogarithmicForm_closed p k X Q g a b hab)

theorem changedResidueClass_eq :
    changedResidueClass p k X Q g a b hab = PDComplex.residueClass p k X Q g a := by
  cases g with
  | zero => rfl
  | succ n =>
      obtain ⟨r, hr⟩ := (PDComplex.topFrame p k X Q (n + 1) a).thickening.p_nilpotent
      have hu : ∀ i,
          (changedCoordinateUnit p k X Q (n + 1) a b hab i :
            (PDComplex.topFrame p k X Q (n + 1) a).thickening.ring) -
          (PDComplex.coordinateUnit p k X Q (n + 1) a i :
            (PDComplex.topFrame p k X Q (n + 1) a).thickening.ring) ∈
          RingHom.ker (PDComplex.topFrame p k X Q (n + 1) a).thickening.reduction := by
        intro i
        rw [changedCoordinateUnit_val, PDComplex.coordinateUnit_val]
        exact coordinate_difference p k X Q (n + 1) a b hab i
      obtain ⟨η, hη⟩ := PD.LogarithmicWedges.Forms.congruent_wedges_exact
        (WittVector p k) (PDComplex.topFrame p k X Q (n + 1) a).thickening.ring
        (RingHom.ker (PDComplex.topFrame p k X Q (n + 1) a).thickening.reduction)
        (PDComplex.topFrame p k X Q (n + 1) a).thickening.dividedPowers p r
        (Fact.out : p.Prime).pos hr n
        (PDComplex.coordinateUnit p k X Q (n + 1) a) (changedCoordinateUnit p k X Q (n + 1) a b hab) hu
      apply AugmentedOrdered.CechTopTotal.topTotalClass_eq
        (PDComplex.family p k X Q (n + 1) a) (PDComplex.localizedComplex p k X Q) (n + 1) (by simp) n
        (changedLogarithmicForm p k X Q (n + 1) a b hab)
        (PDComplex.logarithmicForm p k X Q (n + 1) a)
        (changedLogarithmicForm_closed p k X Q (n + 1) a b hab)
        (PDComplex.logarithmicForm_closed p k X Q (n + 1) a) η
      rw [PDComplex.localizedComplex_d]
      exact hη.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDLiftIndependence.Complex
