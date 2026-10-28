import OAI.Analysis.PDE.Weak.Elliptic.H1

/-! Translation and difference quotients on the genuine H¹ graph closure.
The support statements apply both in the interior and to translations
parallel to a flat Dirichlet boundary. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

def translateH1Pair (a : OAI.Analysis.PDE.Variational.CellCoordinates m) : H1Pair m →L[ℝ] H1Pair m :=
  (translateL2 (V := ℝ) volume a).prodMap (translateL2 (V := OAI.Analysis.PDE.Variational.CellVectors m) volume a)

def differenceH1Pair (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ) : H1Pair m →L[ℝ] H1Pair m :=
  (differenceQuotientL2 (V := ℝ) volume v h).prodMap
    (differenceQuotientL2 (V := OAI.Analysis.PDE.Variational.CellVectors m) volume v h)

theorem cellGradient_translate {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hu : Differentiable ℝ u) (a x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.cellGradient (fun y => u (y + a)) x = OAI.Analysis.PDE.Variational.cellGradient u (x + a) := by
  ext i
  change fderiv ℝ (fun y => u (y + a)) x (Pi.single i 1) = _
  have hh := ((hu (x + a)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const a)).fderiv
  simpa using! congrArg (fun L => L (Pi.single i 1)) hh

theorem translateH1Pair_smooth (a : OAI.Analysis.PDE.Variational.CellCoordinates m) (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u) :
    translateH1Pair a (smoothH1Pair u hu hs) =
      smoothH1Pair (fun x => u (x + a)) (hu.comp (contDiff_id.add contDiff_const))
        (hs.comp_isClosedEmbedding (Homeomorph.addRight a).isClosedEmbedding) := by
  apply Prod.ext
  · change translateL2 volume a _ = _
    apply Lp.ext
    have hv : (smoothH1Pair u hu hs).1 =ᵐ[volume] u :=
      (hu.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp
    have ht := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hv
    filter_upwards [coe_translateL2 volume a (smoothH1Pair u hu hs).1, ht,
      ((hu.comp (contDiff_id.add contDiff_const)).continuous.memLp_of_hasCompactSupport
        (hs.comp_isClosedEmbedding (Homeomorph.addRight a).isClosedEmbedding)).coeFn_toLp]
      with x hx hy hz
    exact hx.trans (hy.trans hz.symm)
  · change translateL2 volume a _ = _
    apply Lp.ext
    have hv : (smoothH1Pair u hu hs).2 =ᵐ[volume] OAI.Analysis.PDE.Variational.cellGradient u :=
      ((OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_cellGradient hs)).coeFn_toLp
    have ht := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hv
    have huc : ContDiff ℝ ∞ (fun x => u (x + a)) := hu.comp (contDiff_id.add contDiff_const)
    have hsc := hs.comp_isClosedEmbedding (Homeomorph.addRight a).isClosedEmbedding
    filter_upwards [coe_translateL2 volume a (smoothH1Pair u hu hs).2, ht,
      ((OAI.Analysis.PDE.Variational.continuous_cellGradient (huc.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_cellGradient hsc)).coeFn_toLp] with x hx hy hz
    exact hx.trans (hy.trans ((cellGradient_translate (hu.differentiable (by simp)) a x).symm.trans hz.symm))

theorem differenceH1Pair_smooth (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ)
    (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u) :
    differenceH1Pair v h (smoothH1Pair u hu hs) =
      smoothH1Pair (differenceQuotient v h u) (contDiff_differenceQuotient v h hu)
        (hasCompactSupport_differenceQuotient hs v h) := by
  apply Prod.ext
  · change differenceQuotientL2 volume v h
      ((hu.continuous.memLp_of_hasCompactSupport hs).toLp u) = _
    rw [differenceQuotientL2_toLp]
    rfl
  · change differenceQuotientL2 volume v h
      (((OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_cellGradient hs)).toLp (OAI.Analysis.PDE.Variational.cellGradient u)) = _
    rw [differenceQuotientL2_toLp]
    apply Lp.ext
    have hg : MemLp (OAI.Analysis.PDE.Variational.cellGradient u) 2 volume :=
      (OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).memLp_of_hasCompactSupport
      (hasCompactSupport_cellGradient hs)
    have huc := contDiff_differenceQuotient v h hu
    have hsc := hasCompactSupport_differenceQuotient hs v h
    filter_upwards [(memLp_differenceQuotient volume v h hg).coeFn_toLp,
      ((OAI.Analysis.PDE.Variational.continuous_cellGradient (huc.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_cellGradient hsc)).coeFn_toLp] with x hx hy
    exact hx.trans ((cellGradient_differenceQuotient v h (hu.differentiable (by simp)) x).symm.trans hy.symm)

theorem H1Zero.translate {Ω Ω' : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {p : H1Pair m}
    (hp : p ∈ H1Zero Ω) (a : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hshift : (fun x => x + a) ⁻¹' Ω ⊆ Ω') :
    translateH1Pair a p ∈ H1Zero Ω' := by
  have hc : IsClosed {q : H1Pair m | translateH1Pair a q ∈ H1Zero Ω'} :=
    isClosed_closure.preimage (translateH1Pair a).continuous
  apply closure_minimal (s := smoothH1Graph Ω) _ hc hp
  rintro q ⟨u, hu, hs, hΩ, rfl⟩
  change translateH1Pair a (smoothH1Pair u hu hs) ∈ H1Zero Ω'
  rw [translateH1Pair_smooth]
  apply smoothH1Pair_mem_H1Zero
  change tsupport (u ∘ (Homeomorph.addRight a)) ⊆ Ω'
  rw [tsupport_comp_eq_preimage u (Homeomorph.addRight a)]
  exact (preimage_mono hΩ).trans hshift

theorem H1Zero.difference {Ω Ω' : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {p : H1Pair m}
    (hp : p ∈ H1Zero Ω) (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ)
    (hsub : Ω ⊆ Ω') (hshift : (fun x => x + h • v) ⁻¹' Ω ⊆ Ω') :
    differenceH1Pair v h p ∈ H1Zero Ω' := by
  have hc : IsClosed {q : H1Pair m | differenceH1Pair v h q ∈ H1Zero Ω'} :=
    isClosed_closure.preimage (differenceH1Pair v h).continuous
  apply closure_minimal (s := smoothH1Graph Ω) _ hc hp
  rintro q ⟨u, hu, hs, hΩ, rfl⟩
  change differenceH1Pair v h (smoothH1Pair u hu hs) ∈ H1Zero Ω'
  rw [differenceH1Pair_smooth]
  apply smoothH1Pair_mem_H1Zero
  exact (tsupport_differenceQuotient_subset u v h).trans
    (union_subset ((preimage_mono hΩ).trans hshift) (hΩ.trans hsub))

theorem H1Zero.tangential_difference
    (ℓ : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ) {p : H1Pair m}
    (hp : p ∈ H1Zero {x | 0 < ℓ x}) (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (hv : ℓ v = 0) (h : ℝ) :
    differenceH1Pair v h p ∈ H1Zero {x | 0 < ℓ x} := by
  apply OAI.Analysis.PDE.Weak.H1Zero.difference hp v h Subset.rfl
  intro x hx
  simpa only [mem_preimage, Set.mem_ofPred_eq, map_add, map_smul, hv, smul_zero, add_zero] using hx

end OAI.Analysis.PDE.Weak
