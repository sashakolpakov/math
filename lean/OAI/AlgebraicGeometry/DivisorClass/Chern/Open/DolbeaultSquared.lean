import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultPrime
import OAI.AlgebraicTopology.DeRham.Comparison.BidegreeIndependence

/-! # Dolbeault Squared -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultSquared

noncomputable section

/-! Square-zero on actual pure open-domain forms, from the original exterior derivative. -/

open _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {U : Opens E} {n p q : ℕ}

omit [IsScalarTower ℝ ℂ E] in
theorem openFormHasBidegree_add {f g : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n}
    (hf : DolbeaultPrime.OpenFormHasBidegree p q f) (hg : DolbeaultPrime.OpenFormHasBidegree p q g) :
    DolbeaultPrime.OpenFormHasBidegree p q (f + g) := by
  intro x z v
  change f x (fun i => (z : ℂ) • v i) + g x (fun i => (z : ℂ) • v i) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * (f x v + g x v)
  rw [hf x z v, hg x z v, mul_add]

theorem openDolbeaultD_squared_of_bidegree (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n)
    (hn : n = p + q) (hf : DolbeaultPrime.OpenFormHasBidegree p q form) :
    DolbeaultOpen.openDolbeaultD (n + 1) (DolbeaultOpen.openDolbeaultD n form) = 0 := by
  have hp := DolbeaultPrime.openDolbeaultPrime_hasBidegree hn hf
  have hd := DolbeaultPrime.openDolbeaultD_hasBidegree hn hf
  have hpp := DolbeaultPrime.openDolbeaultPrime_hasBidegree (by omega : n + 1 = (p + 1) + q) hp
  have hdp := DolbeaultPrime.openDolbeaultD_hasBidegree (by omega : n + 1 = (p + 1) + q) hp
  have hpd := DolbeaultPrime.openDolbeaultPrime_hasBidegree (by omega : n + 1 = p + (q + 1)) hd
  have hdd := DolbeaultPrime.openDolbeaultD_hasBidegree (by omega : n + 1 = p + (q + 1)) hd
  have hmiddle := openFormHasBidegree_add hdp hpd
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  have hsum := congrArg (fun f : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1 + 1) => f x)
    (DolbeaultPrime.openDolbeault_second_sum form)
  exact (AlgebraicTopology.DeRham.Comparison.BidegreeIndependence.formValue_neighbor_triple_eq_zero
    (DolbeaultPrime.openDolbeaultPrime U (n + 1) (DolbeaultPrime.openDolbeaultPrime U n form) x)
    ((DolbeaultOpen.openDolbeaultD (n + 1) (DolbeaultPrime.openDolbeaultPrime U n form) +
      DolbeaultPrime.openDolbeaultPrime U (n + 1) (DolbeaultOpen.openDolbeaultD n form)) x)
    (DolbeaultOpen.openDolbeaultD (n + 1) (DolbeaultOpen.openDolbeaultD n form) x)
    (hpp x) (hmiddle x) (hdd x) hsum).2.2

theorem pureOpenDolbeaultD_squared (U : Opens E) (q : ℕ) (form : DolbeaultPrime.AntiOpenForm U q) :
    DolbeaultPrime.pureOpenDolbeaultD U (q + 1) (DolbeaultPrime.pureOpenDolbeaultD U q form) = 0 :=
  Subtype.ext (openDolbeaultD_squared_of_bidegree form.1 (by omega) form.2)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultSquared
