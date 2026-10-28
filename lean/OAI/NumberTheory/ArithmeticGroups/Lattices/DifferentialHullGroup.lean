import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential
import OAI.NumberTheory.ArithmeticGroups.Lattices.RationalZariski
import OAI.NumberTheory.ArithmeticGroups.Lattices.NoetherianSubmonoid

/-! # Differential Hull Group -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullGroup.Construction

noncomputable section

/-! The algebraic subgroup cut out by the differential core, inside the
rational points of a matrix group. -/

open scoped Classical
open _root_.TopologicalSpace Set

def differentialHullSubmonoid {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k)) :
    Submonoid G.RationalPoints where
  carrier := {g | ∀ p ∈ MatrixDifferential.Construction.matrixDifferentialCore S, Algebraic.evaluateMatrix (RingHom.id k) g.val p = 0}
  one_mem' := fun _ hp => MatrixDifferential.Construction.matrixDifferentialCore_eval_one S hp
  mul_mem' := by
    intro g h hg hh p hp
    have he := hh (LeftTranslation.Construction.leftTranslate (g.val : Matrix (Fin n) (Fin n) k) p)
      (MatrixDifferential.Construction.leftTranslate_mem_matrixDifferentialCore S g.val hg hp)
    rw [MatrixDifferential.Construction.leftTranslate_evaluate_rational] at he
    exact he

theorem differentialHullSubmonoid_closed {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k)) :
    @IsClosed G.RationalPoints (RationalZariski.Construction.rationalZariskiTopology G)
      (differentialHullSubmonoid G S : Set G.RationalPoints) := by
  let : TopologicalSpace G.RationalPoints := RationalZariski.Construction.rationalZariskiTopology G
  have he : (differentialHullSubmonoid G S : Set G.RationalPoints) =
      ⋂ p : MatrixDifferential.Construction.matrixDifferentialCore S,
        {g : G.RationalPoints | Algebraic.evaluateMatrix (RingHom.id k) g.val p.val = 0} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq]
    exact ⟨fun h p => h p.val p.property, fun h p hp => h ⟨p, hp⟩⟩
  rw [he]
  exact isClosed_iInter (fun p => RationalZariski.Construction.rational_polynomial_zero_closed G p.val)

def differentialHullSubgroup {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k)) :
    Subgroup G.RationalPoints := by
  let : TopologicalSpace G.RationalPoints := RationalZariski.Construction.rationalZariskiTopology G
  let : NoetherianSpace G.RationalPoints := RationalZariski.Construction.rational_zariski_noetherian G
  let : SeparatelyContinuousMul G.RationalPoints := {
    continuous_const_mul := fun {g} => RationalZariski.Construction.rational_left_mul_continuous G g
    continuous_mul_const := fun {g} => RationalZariski.Construction.rational_right_mul_continuous G g }
  exact NoetherianSubmonoid.Construction.closedNoetherianSubgroup (differentialHullSubmonoid G S) (differentialHullSubmonoid_closed G S)

theorem mem_differentialHullSubgroup {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k)) (g : G.RationalPoints) :
    g ∈ differentialHullSubgroup G S ↔
      ∀ p ∈ MatrixDifferential.Construction.matrixDifferentialCore S, Algebraic.evaluateMatrix (RingHom.id k) g.val p = 0 := Iff.rfl

def hullVanishingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k)) :
    Ideal (Algebraic.CoordinatePolynomial n k) :=
  ⨅ g : differentialHullSubgroup G S, RingHom.ker (Algebraic.evaluateMatrix (RingHom.id k) g.val.val)

theorem hullVanishingIdeal_eq_core
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k))
    (hS : S ⊆ Infinitesimal.Action.Construction.infinitesimalStabilizer G) : hullVanishingIdeal G S = MatrixDifferential.Construction.matrixDifferentialCore S := by
  apply le_antisymm
  · intro p hp
    apply MatrixDifferential.Construction.matrixDifferentialCore_isRadical S
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro x hx
    have hle := MatrixDifferential.Construction.vanishingIdeal_le_matrixDifferentialCore G S hS
    have hd := hx (CoordinateIdeal.Construction.determinantEquation k n)
      (hle (CoordinateIdeal.Construction.definingIdeal_le_vanishingIdeal G (Ideal.subset_span (Set.mem_insert _ _))))
    have hdet : Matrix.det (fun i j : Fin n => x (i, j)) = 1 := by
      apply sub_eq_zero.mp
      simpa only [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self,
        CoordinateIdeal.Construction.eval_determinantEquation] using hd
    let g : Algebraic.SL n k := ⟨fun i j => x (i, j), hdet⟩
    have hg : g ∈ G.subgroup k (RingHom.id k) := by
      apply (VanishingIdeal.Construction.mem_group_iff_vanishingIdeal G (RingHom.id k) g).mpr
      intro q hq
      exact hx q (hle hq)
    have hh : (⟨g, hg⟩ : G.RationalPoints) ∈ differentialHullSubgroup G S := by
      intro q hq
      exact hx q hq
    exact Ideal.mem_iInf.mp hp ⟨⟨g, hg⟩, hh⟩
  · intro p hp
    apply Ideal.mem_iInf.mpr
    intro g
    exact g.property p hp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullGroup.Construction
