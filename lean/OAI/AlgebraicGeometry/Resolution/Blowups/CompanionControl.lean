import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CompanionOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineEtaleControlTree
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.MaximumOrderTransform

/-! # Companion Control -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CompanionControl.Construction

noncomputable section

/-! Finite actual companion phases with separate residual and exceptional controls. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem blowup_companion_product_factorization {R : Type u} [CommRing R]
    (I J M : Ideal R) (a : I) (m b : ℕ) (hmb : m ≤ b)
    (hJ : J ≤ I ^ m) (hM : M ≤ I ^ (b - m)) :
    ControlledTransform.Construction.blowupControlledTransform I (M * J) b a =
      ControlledTransform.Construction.blowupControlledTransform I M (b - m) a * ControlledTransform.Construction.blowupControlledTransform I J m a := by
  have h := ResidualCoefficientTransform.Construction.blowup_product_controlledTransform I M J a (b - m) m b (by omega) hM hJ
  rw [Nat.sub_add_cancel hmb, Nat.sub_self, pow_zero (Blowup.Charts.Construction.blowupChartConstants I a a.val),
    Ideal.span_singleton_one, Ideal.top_mul] at h
  exact h

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Each node records the unchanged total control, both actual factor
controls, smooth framed centers, and exact product transformation. At leaves
the residual maximum-order stratum misses the unresolved product locus. -/
inductive CompanionControlPhaseTree (k : Type u) [CommRing k] (m b : ℕ) :
    (R : CommRingCat.{u}) → [Algebra k R] → Ideal R → Ideal R → Type (u + 1)
  | terminal {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m = ⊤)
      (hdrop : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (M * J) (b - 1) ⊔
        Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m - 1) = ⊤) :
      CompanionControlPhaseTree k m b R M J
  | refineEtale {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m = ⊤)
      (ι : Type u) [Fintype ι] (S : ι → CommRingCat.{u}) [∀ i, Algebra k (S i)]
      (f : ∀ i, R →ₐ[k] S i) (hf : ∀ i, (f i).toRingHom.Etale)
      (hcover : ∀ p : PrimeSpectrum R, ∃ i, ∃ q : PrimeSpectrum (S i),
        PrimeSpectrum.comap (f i).toRingHom q = p)
      (children : ∀ i, CompanionControlPhaseTree k m b (S i)
        (M.map (f i).toRingHom) (J.map (f i).toRingHom)) :
      CompanionControlPhaseTree k m b R M J
  | blowup {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m = ⊤)
      (I : Ideal R) (hM : M ≤ I ^ (b - m)) (hJ : J ≤ I ^ m) (hprod : M * J ≤ I ^ b)
      (hfactor : ∀ a : I, ControlledTransform.Construction.blowupControlledTransform I (M * J) b a =
        ControlledTransform.Construction.blowupControlledTransform I M (b - m) a * ControlledTransform.Construction.blowupControlledTransform I J m a)
      (hsmooth : Algebra.Smooth k (R ⧸ I))
      (hblowup : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (ι : Type u) [Fintype ι] [DecidableEq ι] (g : ι → I) (D : ι → Derivation k R R)
      (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
      (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I)
      (children : ∀ i, CompanionControlPhaseTree k m b (.of (Blowup.Charts.Construction.blowupChart I (g i)))
        (ControlledTransform.Construction.blowupControlledTransform I M (b - m) (g i)) (ControlledTransform.Construction.blowupControlledTransform I J m (g i))) :
      CompanionControlPhaseTree k m b R M J

def CompanionControlPhaseTree.blowupDepth {k : Type u} [CommRing k] {m b : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
    (T : Construction.CompanionControlPhaseTree k m b R M J) : ℕ := by
  classical
  induction T with
  | terminal hbound hdrop => exact 0
  | refineEtale hbound ι S f hf hcover children ih => exact Finset.univ.sup ih
  | blowup hbound I hM hJ hprod hfactor hsmooth hblowup ι g D hD hgen children ih =>
      exact (Finset.univ.sup ih) + 1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CompanionControl.Construction
