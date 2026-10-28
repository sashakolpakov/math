import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ComputedHomologyNaturality

/-! # Kernel Tower Cech Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechNaturality

noncomputable section

/-! The native Čech dimension shifts and computed tower homology are
natural for genuine compatible maps of coherent kernel towers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))
  {T T' : KernelTowerResolution.Tower (C := X.Modules)}
  [∀ n, (T.object n).IsQuasicoherent] [∀ n, (T.term n).IsQuasicoherent]
  [∀ n, (T'.object n).IsQuasicoherent] [∀ n, (T'.term n).IsQuasicoherent]
  (a : KernelTowerMap.Hom T T')

def sequenceMap (n : ℕ) : T.sequence n ⟶ T'.sequence n where
  τ₁ := a.object (n + 1)
  τ₂ := a.term n
  τ₃ := a.object n
  comm₁₂ := a.inclusion n
  comm₂₃ := a.projection n

def cechSequenceMap (n : ℕ) :
    KernelTowerCechShift.sequence π U T n ⟶ KernelTowerCechShift.sequence π U T' n :=
  (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).mapShortComplex.map (sequenceMap a n)

omit [Fintype ι] in
theorem connecting (n q : ℕ) :
    (KernelTowerCechShift.sequence_shortExact π U hU T n).δ q (q + 1) (by simp) ≫
      (TopCechRightExact.functor π U (q + 1)).map (a.object (n + 1)) =
        (TopCechRightExact.functor π U q).map (a.object n) ≫
          (KernelTowerCechShift.sequence_shortExact π U hU T' n).δ q (q + 1) (by simp) :=
  HomologicalComplex.HomologySequence.δ_naturality (cechSequenceMap π U a n)
    (KernelTowerCechShift.sequence_shortExact π U hU T n)
    (KernelTowerCechShift.sequence_shortExact π U hU T' n) q (q + 1) (by simp)

omit [Fintype ι] in
theorem shift (n q : ℕ)
    (h : IsZero ((TopCechRightExact.functor π U q).obj (T.term n)))
    (h' : IsZero ((TopCechRightExact.functor π U (q + 1)).obj (T.term n)))
    (hT : IsZero ((TopCechRightExact.functor π U q).obj (T'.term n)))
    (hT' : IsZero ((TopCechRightExact.functor π U (q + 1)).obj (T'.term n))) :
    (KernelTowerCechShift.shiftIso π U hU T n q h h').hom ≫
      (TopCechRightExact.functor π U (q + 1)).map (a.object (n + 1)) =
        (TopCechRightExact.functor π U q).map (a.object n) ≫
          (KernelTowerCechShift.shiftIso π U hU T' n q hT hT').hom :=
  connecting π U hU a n q

omit [Fintype ι] in
theorem iteratedShift (q n : ℕ)
    (h : ∀ m < n,
      IsZero ((TopCechRightExact.functor π U (q + m)).obj (T.term m)) ∧
      IsZero ((TopCechRightExact.functor π U (q + m + 1)).obj (T.term m)))
    (h' : ∀ m < n,
      IsZero ((TopCechRightExact.functor π U (q + m)).obj (T'.term m)) ∧
      IsZero ((TopCechRightExact.functor π U (q + m + 1)).obj (T'.term m))) :
    (KernelTowerCechShift.iteratedShiftIso π U hU T q n h).hom ≫
      (TopCechRightExact.functor π U (q + n)).map (a.object n) =
        (TopCechRightExact.functor π U q).map (a.object 0) ≫
          (KernelTowerCechShift.iteratedShiftIso π U hU T' q n h').hom := by
  induction n with
  | zero =>
    change 𝟙 _ ≫ (TopCechRightExact.functor π U q).map (a.object 0) =
      (TopCechRightExact.functor π U q).map (a.object 0) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  | succ n ih =>
    let h0 := fun m hm => h m (Nat.lt_trans hm (Nat.lt_succ_self n))
    let h0' := fun m hm => h' m (Nat.lt_trans hm (Nat.lt_succ_self n))
    let e := KernelTowerCechShift.iteratedShiftIso π U hU T q n h0
    let e' := KernelTowerCechShift.iteratedShiftIso π U hU T' q n h0'
    let s := KernelTowerCechShift.shiftIso π U hU T n (q + n)
      (h n (Nat.lt_succ_self n)).1 (h n (Nat.lt_succ_self n)).2
    let s' := KernelTowerCechShift.shiftIso π U hU T' n (q + n)
      (h' n (Nat.lt_succ_self n)).1 (h' n (Nat.lt_succ_self n)).2
    have hs := shift π U hU a n (q + n)
      (h n (Nat.lt_succ_self n)).1 (h n (Nat.lt_succ_self n)).2
      (h' n (Nat.lt_succ_self n)).1 (h' n (Nat.lt_succ_self n)).2
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun b => e.hom ≫ b) hs).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun b => b ≫ s'.hom) (ih h0 h0')).trans (Category.assoc _ _ _))))

def complexMap (N : ℕ) : KernelTowerCechHomology.complex π U T N ⟶
    KernelTowerCechHomology.complex π U T' N :=
  ((TopCechRightExact.functor π U N).mapHomologicalComplex (.down ℕ)).map a.chainMap

theorem zero (N : ℕ) (hN : Fintype.card ι ≤ N + 1) :
    HomologicalComplex.homologyMap (complexMap π U a N) 0 ≫
      (KernelTowerCechHomology.zeroIso π U hU T' N hN).hom =
        (KernelTowerCechHomology.zeroIso π U hU T N hN).hom ≫
          (TopCechRightExact.functor π U N).map (a.object 0) := by
  let F := TopCechRightExact.functor π U N
  let ep : Epi (F.map (T.projection 0)) := TopCechRightExact.map_epi π U hU N hN (T.projection 0)
  let eq : Epi (F.map (T'.projection 0)) := TopCechRightExact.map_epi π U hU N hN (T'.projection 0)
  have h : F.map (a.term 0) ≫ F.map (T'.projection 0) =
      F.map (T.projection 0) ≫ F.map (a.object 0) :=
    (F.map_comp _ _).symm.trans ((congrArg F.map (a.projection 0)).trans (F.map_comp _ _))
  exact ComputedHomologyNaturality.chainZero (hp_epi := ep) (hq_epi := eq) (complexMap π U a N)
    (F.map (T.projection 0)) _ _ (F.map (T'.projection 0)) _ _ (F.map (a.object 0)) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechNaturality
