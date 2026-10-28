import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionCycleMaps

/-! # Resolution Shift Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionShiftNaturality

noncomputable section

/-! Naturality of the iterated connecting isomorphism of an acyclic resolution. -/
set_option backward.dsimp.instances true
set_option backward.dsimp.proofs true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
namespace IntrinsicCech

private theorem castShift_naturality
    (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (P Q : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, AddCommGroup (Q n)]
    (a : A → B) (v : ∀ n, P n → Q n)
    {i j : ℕ} (e : i = j) (p : A ≃+ P i) (q : B ≃+ Q i) (x : A)
    (h : q (a x) = v i (p x)) :
    (Eq.mpr (congrArg (fun n => B ≃+ Q n) e.symm) q) (a x) =
      v j ((Eq.mpr (congrArg (fun n => A ≃+ P n) e.symm) p) x) := by
  cases e
  exact h

variable {X : TopCat.{u}}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (eK : F ⟶ K.X 0) (wK : eK ≫ K.d 0 1 = 0) [heK : Mono eK]
    (eL : G ⟶ L.X 0) (wL : eL ≫ L.d 0 1 = 0) [heL : Mono eL]
    (haugK : (ShortComplex.mk eK (K.d 0 1) wK).Exact)
    (haugL : (ShortComplex.mk eL (L.d 0 1) wL).Exact)
    (hposK : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).Exact)
    (hposL : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex L n).Exact)
    (hK : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (L.X p) (q + 1)))
    (f : F ⟶ G) (ψ : K ⟶ L) (hψ : f ≫ eL = eK ≫ ψ.f 0)

include hψ heK heL in
private theorem resolutionCycleCohomologyShift_naturality_zero (q : ℕ)
    (x : CategoryTheory.Sheaf.H (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K 0).cycles (q + 1)) :
    AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift L eL wL haugL hposL hL 0 q
        (CategoryTheory.Sheaf.H.map
          (ShortComplex.cyclesMap (ResolutionCycleMaps.IntrinsicCech.resolutionDifferentialShortComplexMap ψ 0)) (q + 1) x) =
      CategoryTheory.Sheaf.H.map f (0 + q + 2)
        (AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift K eK wK haugK hposK hK 0 q x) := by
  have hh := ResolutionCycleMaps.IntrinsicCech.acyclicMiddleCohomologyShift_naturality
    (@AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact X K F eK wK heK haugK hposK)
    (@AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact X L G eL wL heL haugL hposL)
    (ResolutionCycleMaps.IntrinsicCech.initialResolutionCycleSequenceMap eK wK eL wL f ψ hψ) (q + 1)
    (hK 0 q) (hK 0 (q + 1)) (hL 0 q) (hL 0 (q + 1)) x
  let eK0 := AcyclicResolutionDimensionShift.IntrinsicCech.acyclicMiddleCohomologyShift
    (@AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact X K F eK wK heK haugK hposK)
    (q + 1) (hK 0 q) (hK 0 (q + 1))
  let eL0 := AcyclicResolutionDimensionShift.IntrinsicCech.acyclicMiddleCohomologyShift
    (@AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact X L G eL wL heL haugL hposL)
    (q + 1) (hL 0 q) (hL 0 (q + 1))
  have hs := castShift_naturality
    (CategoryTheory.Sheaf.H (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K 0).cycles (q + 1))
    (CategoryTheory.Sheaf.H (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex L 0).cycles (q + 1))
    (fun n => CategoryTheory.Sheaf.H F n)
    (fun n => CategoryTheory.Sheaf.H G n)
    (CategoryTheory.Sheaf.H.map (ShortComplex.cyclesMap (ResolutionCycleMaps.IntrinsicCech.resolutionDifferentialShortComplexMap ψ 0)) (q + 1))
    (fun n => CategoryTheory.Sheaf.H.map f n)
    (by omega : (q + 1) + 1 = 0 + q + 2)
    eK0 eL0 x (by exact hh)
  simp only [eK0, eL0, AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift, Nat.recAux, Nat.rec_zero] at hs ⊢
  exact hs

include hψ heK heL in
theorem resolutionCycleCohomologyShift_naturality (n q : ℕ)
    (x : CategoryTheory.Sheaf.H (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).cycles (q + 1)) :
    AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift L eL wL haugL hposL hL n q
        (CategoryTheory.Sheaf.H.map
          (ShortComplex.cyclesMap (ResolutionCycleMaps.IntrinsicCech.resolutionDifferentialShortComplexMap ψ n)) (q + 1) x) =
      CategoryTheory.Sheaf.H.map f (n + q + 2)
        (AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift K eK wK haugK hposK hK n q x) := by
  induction n generalizing q with
  | zero =>
      exact resolutionCycleCohomologyShift_naturality_zero
        eK wK eL wL haugK haugL hposK hposL hK hL f ψ hψ q x
  | succ n ih =>
      have hd := ResolutionCycleMaps.IntrinsicCech.acyclicMiddleCohomologyShift_naturality
        (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact K hposK n)
        (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact L hposL n)
        (ResolutionCycleMaps.IntrinsicCech.successiveResolutionCycleSequenceMap ψ n) (q + 1)
        (hK (n + 1) q) (hK (n + 1) (q + 1))
        (hL (n + 1) q) (hL (n + 1) (q + 1)) x
      dsimp only [ResolutionCycleMaps.IntrinsicCech.successiveResolutionCycleSequenceMap] at hd
      have hi := ih (q + 1)
        (AcyclicResolutionDimensionShift.IntrinsicCech.acyclicMiddleCohomologyShift
          (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact K hposK n) (q + 1)
          (hK (n + 1) q) (hK (n + 1) (q + 1)) x)
      have hh := (congrArg
        (AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift L eL wL haugL hposL hL n (q + 1)) hd).trans hi
      let eKn := ((AcyclicResolutionDimensionShift.IntrinsicCech.acyclicMiddleCohomologyShift (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact K hposK n)
          (q + 1) (hK (n + 1) q) (hK (n + 1) (q + 1))).trans
            (AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift K eK wK haugK hposK hK n (q + 1)))
      let eLn := ((AcyclicResolutionDimensionShift.IntrinsicCech.acyclicMiddleCohomologyShift (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact L hposL n)
          (q + 1) (hL (n + 1) q) (hL (n + 1) (q + 1))).trans
            (AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift L eL wL haugL hposL hL n (q + 1)))
      have hs := castShift_naturality
        (CategoryTheory.Sheaf.H (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K (n + 1)).cycles (q + 1))
        (CategoryTheory.Sheaf.H (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex L (n + 1)).cycles (q + 1))
        (fun n => CategoryTheory.Sheaf.H F n)
        (fun n => CategoryTheory.Sheaf.H G n)
        (CategoryTheory.Sheaf.H.map (ShortComplex.cyclesMap (ResolutionCycleMaps.IntrinsicCech.resolutionDifferentialShortComplexMap ψ (n + 1))) (q + 1))
        (fun m => CategoryTheory.Sheaf.H.map f m)
        (by omega : n + (q + 1) + 2 = (n + 1) + q + 2)
        eKn eLn x (by exact hh)
      simp only [eKn, eLn, AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift, Nat.recAux] at hs ⊢
      exact hs

end IntrinsicCech

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionShiftNaturality
