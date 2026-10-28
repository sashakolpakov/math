import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.OneCocycleValues
import Mathlib.Algebra.Category.Ring.Basic

/-! # Unit Cech Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechCoefficients

noncomputable section

/-! Actual normalized dual-number transition units give additive
regular Cech cocycles on their original open cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : X.Presheaf CommRingCat.{0})

def ringAdditivePresheaf : X.Presheaf AddCommGrpCat :=
  R ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

def dualCechRestrict {V W : Opens X} (h : W ≤ V)
    (u : (DualNumber (R.obj (op V)))ˣ) : (DualNumber (R.obj (op W)))ˣ :=
  Units.map (NumberCoefficients.dualNumberRingMap (R.map (homOfLE h).op).hom).toMonoidHom u

theorem dualCechRestrict_fst {V W : Opens X} (h : W ≤ V)
    (u : (DualNumber (R.obj (op V)))ˣ) (hu : u.val.fst = 1) :
    (dualCechRestrict R h u).val.fst = 1 := by
  change R.map (homOfLE h).op u.val.fst = 1
  rw [hu, map_one]

theorem dualCechRestrict_snd {V W : Opens X} (h : W ≤ V)
    (u : (DualNumber (R.obj (op V)))ˣ) :
    (dualCechRestrict R h u).val.snd = R.map (homOfLE h).op u.val.snd := rfl

variable {I : Type} (U : I → Opens X)

abbrev DualUnitCechCoefficients := ∀ a : Fin 2 → I,
  (DualNumber (R.obj (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))))ˣ

def dualUnitCechAdditive (u : DualUnitCechCoefficients R U) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (ringAdditivePresheaf R) U 1 :=
  fun a => (u a).val.snd

def DualUnitCechNormalized (u : DualUnitCechCoefficients R U) : Prop :=
  ∀ a, (u a).val.fst = 1

def DualUnitCechCocycle (u : DualUnitCechCoefficients R U) : Prop :=
  ∀ a : Fin 3 → I,
    dualCechRestrict R (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (0 : Fin 3).succAbove)
      (u (a ∘ (0 : Fin 3).succAbove)) *
    dualCechRestrict R (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (2 : Fin 3).succAbove)
      (u (a ∘ (2 : Fin 3).succAbove)) =
    dualCechRestrict R (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (1 : Fin 3).succAbove)
      (u (a ∘ (1 : Fin 3).succAbove))

theorem dualUnitCechAdditive_closed (u : DualUnitCechCoefficients R U)
    (hu : DualUnitCechNormalized R U u) (hc : DualUnitCechCocycle R U u) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (ringAdditivePresheaf R) U 1
      (dualUnitCechAdditive R U u) = 0 := by
  apply Cech.OneCocycleValues.abelianCech_one_closed_of_transition
  intro a
  have h := congrArg (fun v : (DualNumber (R.obj (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))))ˣ => v.val.snd) (hc a)
  rw [UnitCoordinates.dualUnit_snd_mul _ _
    (dualCechRestrict_fst R _ _ (hu _)) (dualCechRestrict_fst R _ _ (hu _))] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechCoefficients
