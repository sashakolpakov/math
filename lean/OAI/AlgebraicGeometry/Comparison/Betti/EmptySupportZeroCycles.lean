import OAI.AlgebraicGeometry.Comparison.Betti.SupportedZeroCycles
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Empty Support Zero Cycles -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.EmptySupportZeroCycles.Cech

noncomputable section

/-! Empty-support degree-zero cycles are precisely constant coefficient families. -/

variable {ι V : Type} [DecidableEq ι] [AddCommGroup V]

def emptySupportConstantCochain (v : V) : SupportedCochains.Cech.supportedCechCochains V (∅ : Finset ι) 0 :=
  ⟨fun _ => v, fun _ h => (h (Finset.empty_subset _)).elim⟩

theorem emptySupportConstantCochain_cycle (v : V) :
    SupportedCochains.Cech.supportedCechDifferential (∅ : Finset ι) 0 (emptySupportConstantCochain v) = 0 := by
  apply Subtype.ext
  funext t
  exact (SupportedZeroCycles.Cech.supportedCechDifferential_zero_apply ∅ (emptySupportConstantCochain v) t).trans (sub_self v)

theorem supportedZeroCycle_eq_constant (N : Finset ι) (s : SupportedCochains.Cech.supportedCechCochains V N 0)
    (hs : SupportedCochains.Cech.supportedCechDifferential N 0 s = 0) (i : ι) (t : Fin 1 → ι) :
    s.val t = s.val (fun _ : Fin 1 => i) := by
  have ht : t = fun _ : Fin 1 => t 0 :=
    funext (fun k => congrArg t (Fin.eq_zero k))
  exact (congrArg s.val ht).trans (SupportedZeroCycles.Cech.supportedZeroCycle_constant N s hs (t 0) i)

def emptySupportZeroCyclesEquiv (i : ι) :
    (SupportedCochains.Cech.supportedCechDifferential (V := V) (∅ : Finset ι) 0).ker ≃+ V where
  toFun s := s.val.val (fun _ => i)
  invFun v := ⟨emptySupportConstantCochain v, emptySupportConstantCochain_cycle v⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    exact (supportedZeroCycle_eq_constant ∅ s.val s.property i t).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.EmptySupportZeroCycles.Cech
