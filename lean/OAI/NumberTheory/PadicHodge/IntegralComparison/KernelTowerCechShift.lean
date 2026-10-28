import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopCechRightExact

/-! # Kernel Tower Cech Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechShift

noncomputable section

/-! Dimension shifting along genuine short exact sequences of scheme
modules, using the connecting maps of their native ordered Čech complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))
  (T : KernelTowerResolution.Tower (C := X.Modules))
  [∀ n, (T.object n).IsQuasicoherent] [∀ n, (T.term n).IsQuasicoherent]

def sequence (n : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ) :=
  (T.sequence n).map (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U)

include hU

omit [Fintype ι] in
theorem sequence_shortExact (n : ℕ) : (KernelTowerCechShift.sequence π U T n).ShortExact := by
  let : (T.sequence n).X₁.IsQuasicoherent :=
    inferInstanceAs ((T.object (n + 1)).IsQuasicoherent)
  let : (T.sequence n).X₂.IsQuasicoherent := inferInstanceAs ((T.term n).IsQuasicoherent)
  let : (T.sequence n).X₃.IsQuasicoherent := inferInstanceAs ((T.object n).IsQuasicoherent)
  exact AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechExact.CategoryTheory.ShortComplex.ShortExact.map_orderedBaseCechComplexFunctor_of_affine_openCover π U hU (T.sequence_shortExact n)

def shiftIso (n q : ℕ)
    (hq : IsZero ((TopCechRightExact.functor π U q).obj (T.term n)))
    (hq' : IsZero ((TopCechRightExact.functor π U (q + 1)).obj (T.term n))) :
    (TopCechRightExact.functor π U q).obj (T.object n) ≅
      (TopCechRightExact.functor π U (q + 1)).obj (T.object (n + 1)) :=
  (KernelTowerCechShift.sequence_shortExact π U hU T n).δIso q (q + 1) (by simp) hq hq'

omit [Fintype ι] in
theorem shiftIso_hom (n q : ℕ)
    (hq : IsZero ((TopCechRightExact.functor π U q).obj (T.term n)))
    (hq' : IsZero ((TopCechRightExact.functor π U (q + 1)).obj (T.term n))) :
    (shiftIso π U hU T n q hq hq').hom =
      (KernelTowerCechShift.sequence_shortExact π U hU T n).δ q (q + 1) (by simp) := rfl

def iteratedShiftIso (q n : ℕ)
    (h : ∀ m < n,
      IsZero ((TopCechRightExact.functor π U (q + m)).obj (T.term m)) ∧
      IsZero ((TopCechRightExact.functor π U (q + m + 1)).obj (T.term m))) :
    (TopCechRightExact.functor π U q).obj (T.object 0) ≅
      (TopCechRightExact.functor π U (q + n)).obj (T.object n) := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih =>
    exact ih (fun m hm => h m (Nat.lt_trans hm (Nat.lt_succ_self n))) ≪≫
      shiftIso π U hU T n (q + n) (h n (Nat.lt_succ_self n)).1 (h n (Nat.lt_succ_self n)).2

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechShift
