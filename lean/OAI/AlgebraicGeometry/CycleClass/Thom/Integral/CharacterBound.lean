import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.CharacterClosed
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice

/-! # Character Bound -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.CharacterBound.Constructions

noncomputable section

/-! Monic integral equations bound every source evaluation over a compact
set of base characters. This is the compactness input for finite maps. -/

open _root_.Polynomial
open scoped NNReal

variable {A B : Type*} [CommRing A] [Algebra ℂ A]
  [CommRing B] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]

def monicCharacterBound (p : A[X]) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : ℝ≥0 :=
  (Finset.range p.natDegree).sup (fun i => ‖x (p.coeff i)‖₊) + 1

theorem monicCharacterBound_continuous (p : A[X]) : Continuous (monicCharacterBound p) :=
  (Continuous.finset_sup_apply (fun i _ =>
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (p.coeff i)).nnnorm)).add continuous_const

theorem monicCharacterBound_eq (p : A[X]) (hp : p.Monic) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    monicCharacterBound p x = (p.map x.toRingHom).cauchyBound := by
  simp only [monicCharacterBound, Polynomial.cauchyBound, hp.natDegree_map,
    (hp.map x.toRingHom).leadingCoeff, nnnorm_one, div_one, coeff_map]
  rfl

theorem integralCharacter_norm_bound (K : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) (hK : IsCompact K)
    (b : B) (hb : IsIntegral A b) :
    ∃ r : ℝ≥0, ∀ y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B,
      y.comp (IsScalarTower.toAlgHom ℂ A B) ∈ K → ‖y b‖₊ ≤ r := by
  obtain ⟨p, hp, hpb⟩ := hb
  obtain ⟨r, hr⟩ := hK.bddAbove_image (monicCharacterBound_continuous p).continuousOn
  refine ⟨r, fun y hy => ?_⟩
  let x := y.comp (IsScalarTower.toAlgHom ℂ A B)
  have hroot : (p.map x.toRingHom).IsRoot (y b) := by
    rw [Polynomial.IsRoot, eval_map]
    change p.eval₂ (y.toRingHom.comp (algebraMap A B)) (y b) = 0
    have he := Polynomial.hom_eval₂ p (algebraMap A B) y.toRingHom b
    exact he.symm.trans (by rw [hpb, map_zero])
  have h := hroot.norm_lt_cauchyBound (hp.map x.toRingHom).ne_zero
  rw [← monicCharacterBound_eq p hp x] at h
  exact h.le.trans (hr (Set.mem_image_of_mem _ hy))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.CharacterBound.Constructions
