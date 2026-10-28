import OAI.RepresentationTheory.Weil.UnitarySplitting.ComplementIsometry
import OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport

/-! # Standard Transvections -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.StandardTransvections.Construction

noncomputable section

/-! The standard symplectic form and rank-one transvections in the
coordinates used by the Schrödinger representation. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.ComplementIsometry.Transvections _root_.Matrix
open scoped BigOperators

def standardSymplecticBilinear (F : Type) [NormedField F] (d : ℕ) :
    LinearMap.BilinForm F (Local.FunctionsMetaplectic.Construction.PhaseSpace F d) where
  toFun v :=
    { toFun := Oscillator.Construction.standardSymplecticPairing d v
      map_add' x y := by
        unfold Oscillator.Construction.standardSymplecticPairing
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.add_apply]
        ring
      map_smul' a x := by
        unfold Oscillator.Construction.standardSymplecticPairing
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change Oscillator.Construction.standardSymplecticPairing d (v + w) x =
      Oscillator.Construction.standardSymplecticPairing d v x + Oscillator.Construction.standardSymplecticPairing d w x
    unfold Oscillator.Construction.standardSymplecticPairing
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply]
    ring
  map_smul' a v := by
    apply LinearMap.ext
    intro x
    change Oscillator.Construction.standardSymplecticPairing d (a • v) x = a * Oscillator.Construction.standardSymplecticPairing d v x
    unfold Oscillator.Construction.standardSymplecticPairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem standardSymplecticBilinear_apply {F : Type} [NormedField F] (d : ℕ)
    (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : standardSymplecticBilinear F d v w = Oscillator.Construction.standardSymplecticPairing d v w := rfl

theorem standardSymplecticBilinear_alternating {F : Type} [NormedField F] (d : ℕ) :
    (standardSymplecticBilinear F d).IsAlt := by
  intro v
  change Oscillator.Construction.standardSymplecticPairing d v v = 0
  unfold Oscillator.Construction.standardSymplecticPairing
  apply Finset.sum_eq_zero
  intro i _
  ring

theorem standardSymplecticBilinear_nondegenerate {F : Type} [NormedField F] (d : ℕ) :
    (standardSymplecticBilinear F d).Nondegenerate := by
  classical
  have hleft (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (hv : ∀ w, standardSymplecticBilinear F d v w = 0) : v = 0 := by
    funext i
    cases i with
    | inl j =>
        have hh := hv (Pi.single (Sum.inr j) 1)
        have hh' : -v (Sum.inl j) = 0 := by
          simpa [standardSymplecticBilinear_apply, Oscillator.Construction.standardSymplecticPairing, Pi.single_apply] using hh
        exact neg_eq_zero.mp hh'
    | inr j =>
        have hh := hv (Pi.single (Sum.inl j) 1)
        simpa [standardSymplecticBilinear_apply, Oscillator.Construction.standardSymplecticPairing, Pi.single_apply] using hh
  constructor
  · exact hleft
  · intro v hv
    apply hleft v
    intro w
    exact (standardSymplecticBilinear_alternating d).eq_iff.mp (hv w)

def standardTransvection {F : Type} [NormedField F] {d : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (a : F) :
    FrameTransport.Construction.StandardSymplectic F d :=
  DualPair.Transvections.transvection (standardSymplecticBilinear F d) (standardSymplecticBilinear_alternating d) v a

theorem standardTransvection_apply {F : Type} [NormedField F] {d : ℕ}
    (v x : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (a : F) :
    (standardTransvection v a).val x = x + (a * Oscillator.Construction.standardSymplecticPairing d v x) • v :=
  DualPair.Transvections.transvection_apply (standardSymplecticBilinear F d) (standardSymplecticBilinear_alternating d) v x a

def rankOneSymmetric {F : Type} [Field F] {d : ℕ} (p : Local.FunctionsMetaplectic.Construction.Position F d) (a : F) : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F d :=
  ⟨fun i j => a * p i * p j, by
    ext i j
    change a * p j * p i = a * p i * p j
    ring⟩

theorem standardTransvection_momentum {F : Type} [NormedField F] {d : ℕ}
    (p : Local.FunctionsMetaplectic.Construction.Position F d) (a : F) :
    standardTransvection (Sum.elim 0 p) a = FrameTransport.Construction.shearSymplectic (rankOneSymmetric p a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [standardTransvection_apply]
  funext i
  cases i with
  | inl j => simp [FrameTransport.Construction.shearSymplectic, FrameTransport.Construction.shearLinearEquiv, FrameTransport.Construction.shearFunction, FourierCovariance.Construction.phasePosition]
  | inr j =>
      change x (Sum.inr j) + (a * Oscillator.Construction.standardSymplecticPairing d (Sum.elim 0 p) x) * p j =
        (∑ k, a * p j * p k * x (Sum.inl k)) + x (Sum.inr j)
      simp only [Oscillator.Construction.standardSymplecticPairing, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply,
        zero_mul, sub_zero]
      rw [add_comm]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem exists_symmetric_mulVec {F : Type} [Field F] {d : ℕ}
    (q p : Local.FunctionsMetaplectic.Construction.Position F d) (hq : q ≠ 0) :
    ∃ B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F d, B.val *ᵥ q = p := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra! h
    exact hq (funext h)
  let w : Local.FunctionsMetaplectic.Construction.Position F d := Pi.single i (q i)⁻¹
  have hw : w ⬝ᵥ q = 1 := by
    simp [w, dotProduct, Pi.single_apply, hi]
  let B : Matrix (Fin d) (Fin d) F := Matrix.vecMulVec p w + Matrix.vecMulVec w p -
    (p ⬝ᵥ q) • Matrix.vecMulVec w w
  have hsymm : B.IsSymm := by
    ext j k
    change p k * w j + w k * p j - (p ⬝ᵥ q) * (w k * w j) =
      p j * w k + w j * p k - (p ⬝ᵥ q) * (w j * w k)
    ring
  refine ⟨⟨B, hsymm⟩, ?_⟩
  change B *ᵥ q = p
  dsimp [B]
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, hw]
  funext j
  change p j * 1 + w j * (p ⬝ᵥ q) - (p ⬝ᵥ q) * (w j * 1) = p j
  ring

theorem standardTransvection_conjugation {F : Type} [NormedField F] {d : ℕ}
    (g : FrameTransport.Construction.StandardSymplectic F d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (a : F) :
    g * standardTransvection v a * g⁻¹ = standardTransvection (g.val v) a :=
  DualPair.Transvections.transvection_conjugation (standardSymplecticBilinear F d)
    (standardSymplecticBilinear_alternating d) g v a

theorem shear_rotation_sends {F : Type} [NormedField F] {d : ℕ}
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (hq : FourierCovariance.Construction.phasePosition v ≠ 0) :
    ∃ B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F d,
      (FrameTransport.Construction.shearSymplectic B * FrameTransport.Construction.rotationSymplectic d).val (Sum.elim 0 (FourierCovariance.Construction.phasePosition v)) = v := by
  obtain ⟨B, hB⟩ := exists_symmetric_mulVec (FourierCovariance.Construction.phasePosition v) (FourierCovariance.Construction.phaseMomentum v) hq
  refine ⟨B, ?_⟩
  funext i
  cases i with
  | inl j => rfl
  | inr j =>
      change (B.val *ᵥ FourierCovariance.Construction.phasePosition v) j + -(0 : F) = v (Sum.inr j)
      rw [neg_zero, add_zero, hB]
      rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.StandardTransvections.Construction
