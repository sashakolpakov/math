import OAI.AlgebraicGeometry.Resolution.Blowups.CompanionControl

/-! # Residual Control -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ResidualControl.Construction

noncomputable section

/-! Actual residual-order phases with exact product control and explicitly tracked remaining factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The tracked factor is updated by an explicit ideal on each actual
chart. Its product with the residual transform is exactly the original
product's fixed-control transform. Terminal leaves have smaller residual
order everywhere that the product is still unresolved. -/
inductive ResidualControlPhaseTree (k : Type u) [CommRing k] (m b : ℕ) :
    (R : CommRingCat.{u}) → [Algebra k R] → Ideal R → Ideal R → Type (u + 1)
  | terminal {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m = ⊤)
      (hdrop : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (M * J) (b - 1) ⊔
        Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m - 1) = ⊤) :
      ResidualControlPhaseTree k m b R M J
  | refineEtale {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m = ⊤)
      (ι : Type u) [Fintype ι] (S : ι → CommRingCat.{u}) [∀ i, Algebra k (S i)]
      (f : ∀ i, R →ₐ[k] S i) (hf : ∀ i, (f i).toRingHom.Etale)
      (hcover : ∀ p : PrimeSpectrum R, ∃ i, ∃ q : PrimeSpectrum (S i),
        PrimeSpectrum.comap (f i).toRingHom q = p)
      (children : ∀ i, ResidualControlPhaseTree k m b (S i)
        (M.map (f i).toRingHom) (J.map (f i).toRingHom)) :
      ResidualControlPhaseTree k m b R M J
  | blowup {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m = ⊤)
      (I : Ideal R) (hJ : J ≤ I ^ m) (hprod : M * J ≤ I ^ b)
      (M' : ∀ a : I, Ideal (Blowup.Charts.Construction.blowupChart I a))
      (hfactor : ∀ a : I, ControlledTransform.Construction.blowupControlledTransform I (M * J) b a =
        M' a * ControlledTransform.Construction.blowupControlledTransform I J m a)
      (hsmooth : Algebra.Smooth k (R ⧸ I))
      (hblowup : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (ι : Type u) [Fintype ι] [DecidableEq ι] (g : ι → I) (D : ι → Derivation k R R)
      (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
      (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I)
      (children : ∀ i, ResidualControlPhaseTree k m b (.of (Blowup.Charts.Construction.blowupChart I (g i)))
        (M' (g i)) (ControlledTransform.Construction.blowupControlledTransform I J m (g i))) :
      ResidualControlPhaseTree k m b R M J

def ResidualControlPhaseTree.blowupDepth {k : Type u} [CommRing k] {m b : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
    (T : Construction.ResidualControlPhaseTree k m b R M J) : ℕ := by
  classical
  induction T with
  | terminal hbound hdrop => exact 0
  | refineEtale hbound ι S f hf hcover children ih => exact Finset.univ.sup ih
  | blowup hbound I hJ hprod M' hfactor hsmooth hblowup ι g D hD hgen children ih =>
      exact (Finset.univ.sup ih) + 1

/-- Companion phases are residual phases with their separately controlled
factor as the explicit next factor; all actual centers and depths are retained. -/
theorem exists_residual_phase_of_companion_phase (k : Type u) [CommRing k]
    {m b : ℕ} {R : CommRingCat.{u}} [Algebra k R] {M J : Ideal R}
    (T : CompanionControl.Construction.CompanionControlPhaseTree k m b R M J) :
    ∃ S : Construction.ResidualControlPhaseTree k m b R M J, S.blowupDepth = T.blowupDepth := by
  classical
  induction T with
  | terminal hbound hdrop => exact ⟨.terminal hbound hdrop, rfl⟩
  | refineEtale hbound ι A f hf hcover children ih =>
      refine ⟨.refineEtale hbound ι A f hf hcover (fun i => (ih i).choose), ?_⟩
      change (Finset.univ.sup fun i => (ih i).choose.blowupDepth) =
        (Finset.univ.sup fun i => (children i).blowupDepth)
      exact Finset.sup_congr rfl (fun i _ => (ih i).choose_spec)
  | @blowup R _ M J hbound I hM hJ hprod hfactor hsmooth hblowup ι _ _ g D hD hgen children ih =>
      refine ⟨.blowup hbound I hJ hprod (fun a => ControlledTransform.Construction.blowupControlledTransform I M (b - m) a)
        hfactor hsmooth hblowup ι g D hD hgen (fun i => (ih i).choose), ?_⟩
      change (Finset.univ.sup fun i => (ih i).choose.blowupDepth) + 1 =
        (Finset.univ.sup fun i => (children i).blowupDepth) + 1
      congr 1
      exact Finset.sup_congr rfl (fun i _ => (ih i).choose_spec)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ResidualControl.Construction
