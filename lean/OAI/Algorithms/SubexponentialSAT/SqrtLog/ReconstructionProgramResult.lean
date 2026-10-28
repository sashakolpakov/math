import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTAtZero
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction

namespace OAI.Algorithms

/-! Exact semantic readback for the scalar returned by the native CRT loop,
in the ring defined by the actual searched polynomial. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT Polynomial

variable {d : ℕ} (model : RingModel.Data d) (t : ℕ) (ht : 0 < t)

/-- Distinct residue nodes certify the unit differences required by Hermite
uniqueness, also in the presence of nilpotents in the coefficient ring. -/
theorem model_unit_differences {Q : ℕ} (theta : Fin Q → model.O t)
    (h : Function.Injective (fun i => model.rho t ht (theta i))) :
    Pairwise (fun i j => IsUnit (theta i - theta j)) := by
  intro i j hij
  apply model.isUnit_of_rho_ne_zero t ht
  rw [map_sub, sub_ne_zero]
  exact fun he => hij (h he)

theorem scalar_value_eq_target {Q : ℕ} [NeZero Q]
    (theta : Fin Q → model.O t) (J : ℕ) (hJ : 0 < J)
    (hnodes : Function.Injective (fun i => model.rho t ht (theta i)))
    (inverse : Fin Q → model.O t) (jets : Fin Q → (model.O t)[X])
    (hinverse : ∀ i, inverse i * (TruncatedInverse.localFactor theta J i).coeff 0 = 1)
    (target : (model.O t)[X]) (hdegree : target.natDegree < Q * J)
    (hjets : ∀ i, Truncation.trunc J (jets i) = JetCRT.jet (theta i) J target) :
    SubexpCRTAtZero.value theta J inverse jets = target.eval 0 := by
  let _ : Nontrivial (model.O t) := (model.rho t ht).domain_nontrivial
  exact SubexpCRTAtZero.value_eq_target theta J hJ
    (model_unit_differences model t ht theta hnodes) inverse jets hinverse target
    (by simpa using hdegree) hjets

/-- Scalar readback is exact under the independently chosen p-adic precision. -/
theorem scalar_decode_count (hd : d ≠ 0) (output : model.O t)
    (count m n : ℕ) (hcount : count ≤ m * 2^n) (hprecision : m * 2^n < 3^t)
    (hout : output = (count : model.O t)) :
    model.decodeCount t ht output = count := by
  rw [hout]
  exact model.decodeCount_natCast t ht hd count (hcount.trans_lt hprecision)

include ht in
theorem scalar_zero_iff (hd : d ≠ 0) (output : model.O t)
    (count m n : ℕ) (hcount : count ≤ m * 2^n) (hprecision : m * 2^n < 3^t)
    (hout : output = (count : model.O t)) : output = 0 ↔ count = 0 := by
  rw [hout]
  exact model.count_eq_zero_iff t ht hd count (hcount.trans_lt hprecision)

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end

end OAI.Algorithms
