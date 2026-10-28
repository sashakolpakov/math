import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Single

/-! # Hodge Truncation Is -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationIs.HodgeTruncationLayer

noncomputable section

/-! # Successive original Hodge truncations have the actual single-term quotients -/

open _root_.CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℕ)

theorem below (r n : ℕ) (h : n < r) : IsZero ((HodgeFiltrationD.HodgeFiltration.brutal K r).X n) := by
  change IsZero (HodgeFiltrationD.HodgeFiltration.term K r n)
  rw [HodgeFiltrationD.HodgeFiltration.term, ite_eq_right (by omega)]
  exact isZero_zero C

theorem inclusion_isIso (r n : ℕ) (h : r ≤ n) : IsIso ((HodgeFiltrationD.HodgeFiltration.inclusion K r).f n) := by
  change IsIso (HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n)
  rw [HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left (by omega)]
  infer_instance

def layer (r : ℕ) : CochainComplex C ℕ :=
  (HomologicalComplex.single C (.up ℕ) r).obj (K.X r)

def projection (r : ℕ) : HodgeFiltrationD.HodgeFiltration.brutal K r ⟶ layer K r :=
  HomologicalComplex.mkHomToSingle ((HodgeFiltrationD.HodgeFiltration.inclusion K r).f r) (by
    intro i hi
    change i + 1 = r at hi
    exact (below K r i (by omega)).eq_of_src _ _)

theorem projection_isIso (r : ℕ) : IsIso ((projection K r).f r) := by
  rw [projection, HomologicalComplex.mkHomToSingle_f]
  exact IsIso.comp_isIso' (inclusion_isIso K r r le_rfl)
    (HomologicalComplex.singleObjXSelf (.up ℕ) r (K.X r)).isIso_inv

def transition (r : ℕ) : HodgeFiltrationD.HodgeFiltration.brutal K (r + 1) ⟶ HodgeFiltrationD.HodgeFiltration.brutal K r :=
  HodgeFiltrationD.HodgeFiltration.transition K (show (r : ℤ) ≤ ((r + 1 : ℕ) : ℤ) by omega)

theorem transition_projection (r : ℕ) : transition K r ≫ projection K r = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  exact (below K (r + 1) r (Nat.lt_succ_self r)).eq_of_src _ _

def sequence (r : ℕ) : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (transition K r) (projection K r) (transition_projection K r)

theorem transition_isIso (r n : ℕ) (hne : n ≠ r) : IsIso ((transition K r).f n) := by
  by_cases h : r + 1 ≤ n
  · change IsIso (HodgeFiltrationD.HodgeFiltration.transitionTerm K
      (show (r : ℤ) ≤ ((r + 1 : ℕ) : ℤ) by omega) n)
    rw [HodgeFiltrationD.HodgeFiltration.transitionTerm, dite_eq_left (by omega)]
    infer_instance
  · exact (below K (r + 1) n (by omega)).isIso (below K r n (by omega)) _

theorem shortExact (r : ℕ) : (sequence K r).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  by_cases h : n = r
  · subst n
    exact (ShortComplex.Splitting.ofIsZeroOfIsIso _
      (below K (r + 1) r (Nat.lt_succ_self r)) (projection_isIso K r)).shortExact
  · exact (ShortComplex.Splitting.ofIsIsoOfIsZero _ (transition_isIso K r n h)
      (HomologicalComplex.isZero_single_obj_X (.up ℕ) r (K.X r) n h)).shortExact

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationIs.HodgeTruncationLayer
