import OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochains
import Mathlib.Data.Fin.Basic

/-! # Supported Zero Cycles -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SupportedZeroCycles.Cech

noncomputable section

/-! Degree-zero supported cocycles are constant, and nonempty supports vanish on a nontrivial cover. -/

variable {ι V : Type} [DecidableEq ι] [AddCommGroup V]

omit [DecidableEq ι] in
theorem supportCechDelete_pair_zero (t : Fin 2 → ι) :
    SupportedCochains.Cech.supportCechDelete t 0 = fun _ : Fin 1 => t 1 := by
  funext k
  have hk : k = 0 := Fin.eq_zero k
  subst k
  rfl

omit [DecidableEq ι] in
theorem supportCechDelete_pair_one (t : Fin 2 → ι) :
    SupportedCochains.Cech.supportCechDelete t 1 = fun _ : Fin 1 => t 0 := by
  funext k
  have hk : k = 0 := Fin.eq_zero k
  subst k
  rfl

theorem supportedCechDifferential_zero_apply (N : Finset ι) (s : SupportedCochains.Cech.supportedCechCochains V N 0)
    (t : Fin 2 → ι) :
    (SupportedCochains.Cech.supportedCechDifferential N 0 s).val t =
      s.val (fun _ : Fin 1 => t 1) - s.val (fun _ : Fin 1 => t 0) := by
  rw [SupportedCochains.Cech.supportedCechDifferential_apply, Fin.sum_univ_two, supportCechDelete_pair_zero,
    supportCechDelete_pair_one]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul,
    sub_eq_add_neg, add_comm]

theorem supportedZeroCycle_constant (N : Finset ι) (s : SupportedCochains.Cech.supportedCechCochains V N 0)
    (hs : SupportedCochains.Cech.supportedCechDifferential N 0 s = 0) (i j : ι) :
    s.val (fun _ : Fin 1 => i) = s.val (fun _ : Fin 1 => j) := by
  let t : Fin 2 → ι := Fin.cases j (fun _ => i)
  have h := congrArg (fun a : SupportedCochains.Cech.supportedCechCochains V N 1 => a.val t) hs
  have hd := supportedCechDifferential_zero_apply N s t
  exact sub_eq_zero.mp (hd.symm.trans h)

theorem supportedZeroCycle_zero_of_nonempty [Nontrivial ι] (N : Finset ι) (hN : N.Nonempty)
    (s : SupportedCochains.Cech.supportedCechCochains V N 0) (hs : SupportedCochains.Cech.supportedCechDifferential N 0 s = 0) : s = 0 := by
  obtain ⟨i, hi⟩ := hN
  obtain ⟨j, hji⟩ := exists_ne i
  have hj : ¬N ⊆ Finset.univ.image (fun _ : Fin 1 => j) := by
    intro h
    obtain ⟨_, _, h⟩ := Finset.mem_image.mp (h hi)
    exact hji h
  have hz := s.property (fun _ : Fin 1 => j) hj
  apply Subtype.ext
  funext t
  have ht : t = fun _ : Fin 1 => t 0 :=
    funext (fun k => congrArg t (Fin.eq_zero k))
  exact (congrArg s.val ht).trans ((supportedZeroCycle_constant N s hs (t 0) j).trans hz)

end

end OAI.AlgebraicGeometry.Comparison.Betti.SupportedZeroCycles.Cech
