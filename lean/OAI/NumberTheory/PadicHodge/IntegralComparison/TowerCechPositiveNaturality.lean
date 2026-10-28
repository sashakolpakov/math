import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechNaturality

/-! # Tower Cech Positive Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TowerCechPositiveNaturality.Kernel

noncomputable section

/-! Naturality of the positive-degree and shifted native Čech homology
coordinates of coherent kernel towers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))
  {T T' : KernelTowerResolution.Tower (C := X.Modules)}
  [∀ n, (T.object n).IsQuasicoherent] [∀ n, (T.term n).IsQuasicoherent]
  [∀ n, (T'.object n).IsQuasicoherent] [∀ n, (T'.term n).IsQuasicoherent]
  (a : KernelTowerMap.Hom T T')

theorem positive (n : ℕ) (hn : Fintype.card ι ≤ n + 2)
    (hz : ∀ j, IsZero ((TopCechRightExact.functor π U n).obj (T.term j)))
    (hz' : ∀ j, IsZero ((TopCechRightExact.functor π U n).obj (T'.term j))) (i : ℕ) :
    HomologicalComplex.homologyMap (KernelTowerCechNaturality.complexMap π U a (n + 1)) (i + 1) ≫
      (KernelTowerCechHomology.positiveIso π U hU T' n hn hz' i).hom =
        (KernelTowerCechHomology.positiveIso π U hU T n hn hz i).hom ≫
          (TopCechRightExact.functor π U n).map (a.object i) := by
  let F := TopCechRightExact.functor π U (n + 1)
  let K := KernelTowerCechHomology.complex π U T (n + 1)
  let K' := KernelTowerCechHomology.complex π U T' (n + 1)
  let f := KernelTowerCechNaturality.complexMap π U a (n + 1)
  let ep : Epi (F.map (T.projection (i + 1))) :=
    TopCechRightExact.map_epi π U hU (n + 1) hn (T.projection (i + 1))
  let ep' : Epi (F.map (T'.projection (i + 1))) :=
    TopCechRightExact.map_epi π U hU (n + 1) hn (T'.projection (i + 1))
  let mi : Mono ((KernelTowerCechShift.sequence_shortExact π U hU T i).δ n (n + 1) (by simp)) :=
    (KernelTowerCechShift.sequence_shortExact π U hU T i).mono_δ n (n + 1) (by simp) (hz i)
  let mi' : Mono ((KernelTowerCechShift.sequence_shortExact π U hU T' i).δ n (n + 1) (by simp)) :=
    (KernelTowerCechShift.sequence_shortExact π U hU T' i).mono_δ n (n + 1) (by simp) (hz' i)
  dsimp only [KernelTowerCechHomology.positiveIso, Iso.trans_hom]
  rw [← Category.assoc, ComputedHomologyNaturality.shortComplex]
  simp only [Category.assoc]
  apply congrArg (fun b => (K.homologyIsoSc' (i + 1 + 1) (i + 1) i (by simp) (by simp)).hom ≫ b)
  apply ComputedHomologyNaturality.cokernelKernel
    (ep := ep) (ep' := ep') (mi := mi) (mi' := mi')
    (q := F.map (a.object (i + 1)))
    (h := (TopCechRightExact.functor π U n).map (a.object i))
  · exact (F.map_comp _ _).symm.trans
      ((congrArg F.map (a.projection (i + 1)).symm).trans (F.map_comp _ _))
  · exact (F.map_comp _ _).symm.trans
      ((congrArg F.map (a.inclusion i)).trans (F.map_comp _ _))
  · exact (KernelTowerCechNaturality.connecting π U hU a i n).symm

private theorem invert_square {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : e.hom ≫ b = a ≫ e'.hom) : b ≫ e'.inv = e.inv ≫ a := by
  have H := congrArg (fun f => e.inv ≫ f ≫ e'.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using H

theorem shiftedPositive (q i : ℕ) (hn : Fintype.card ι ≤ q + i + 2)
    (hz : ∀ r < q + i + 1, ∀ j,
      IsZero ((TopCechRightExact.functor π U r).obj (T.term j)))
    (hz' : ∀ r < q + i + 1, ∀ j,
      IsZero ((TopCechRightExact.functor π U r).obj (T'.term j))) :
    HomologicalComplex.homologyMap (KernelTowerCechNaturality.complexMap π U a (q + i + 1)) (i + 1) ≫
      (KernelTowerCechHomology.shiftedPositiveIso π U hU T' q i hn hz').hom =
        (KernelTowerCechHomology.shiftedPositiveIso π U hU T q i hn hz).hom ≫
          (TopCechRightExact.functor π U q).map (a.object 0) := by
  let h : ∀ m < i,
      IsZero ((TopCechRightExact.functor π U (q + m)).obj (T.term m)) ∧
      IsZero ((TopCechRightExact.functor π U (q + m + 1)).obj (T.term m)) :=
    fun m hm => ⟨hz (q + m) (by omega) m, hz (q + m + 1) (by omega) m⟩
  let h' : ∀ m < i,
      IsZero ((TopCechRightExact.functor π U (q + m)).obj (T'.term m)) ∧
      IsZero ((TopCechRightExact.functor π U (q + m + 1)).obj (T'.term m)) :=
    fun m hm => ⟨hz' (q + m) (by omega) m, hz' (q + m + 1) (by omega) m⟩
  have H := invert_square
    (KernelTowerCechShift.iteratedShiftIso π U hU T q i h)
    (KernelTowerCechShift.iteratedShiftIso π U hU T' q i h')
    ((TopCechRightExact.functor π U q).map (a.object 0))
    ((TopCechRightExact.functor π U (q + i)).map (a.object i))
    (KernelTowerCechNaturality.iteratedShift π U hU a q i h h')
  dsimp only [KernelTowerCechHomology.shiftedPositiveIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, positive π U hU a, Category.assoc, H, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TowerCechPositiveNaturality.Kernel
