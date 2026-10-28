import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FramedOpenControlTree

/-! # Affine Etale Control Tree -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineEtaleControlTree.Construction

noncomputable section

/-! Finite actual smooth blowup trees with jointly surjective étale refinements. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Every center has an explicit dual coordinate frame and is permissible
and smooth, every whole blowup is smooth,
and every refinement is a finite jointly surjective family of actual étale
maps. Terminal leaves have empty order locus at the unchanged control. -/
inductive SmoothAffineEtaleControlTree (k : Type u) [CommRing k] (b : ℕ) :
    (R : CommRingCat.{u}) → [Algebra k R] → Ideal R → Type (u + 1)
  | terminal {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (hterminal : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (b - 1) = ⊤) :
      SmoothAffineEtaleControlTree k b R J
  | refineEtale {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (ι : Type u) [Fintype ι] (S : ι → CommRingCat.{u}) [∀ i, Algebra k (S i)]
      (f : ∀ i, R →ₐ[k] S i) (hf : ∀ i, (f i).toRingHom.Etale)
      (hcover : ∀ p : PrimeSpectrum R, ∃ i, ∃ q : PrimeSpectrum (S i),
        PrimeSpectrum.comap (f i).toRingHom q = p)
      (children : ∀ i, SmoothAffineEtaleControlTree k b (S i) (J.map (f i).toRingHom)) :
      SmoothAffineEtaleControlTree k b R J
  | blowup {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (I : Ideal R) (hb : 0 < b) (hperm : J ≤ I ^ b)
      (hsmooth : Algebra.Smooth k (R ⧸ I))
      (hblowup : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (ι : Type u) [Fintype ι] [DecidableEq ι] (g : ι → I)
      (D : ι → Derivation k R R)
      (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
      (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I)
      (children : ∀ i, SmoothAffineEtaleControlTree k b (.of (Blowup.Charts.Construction.blowupChart I (g i)))
        (ControlledTransform.Construction.blowupControlledTransform I J b (g i))) :
      SmoothAffineEtaleControlTree k b R J

def SmoothAffineEtaleControlTree.blowupDepth {k : Type u} [CommRing k] {b : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
    (T : Construction.SmoothAffineEtaleControlTree k b R J) : ℕ := by
  classical
  induction T with
  | terminal ht => exact 0
  | refineEtale ι S f hf hcover children ih => exact Finset.univ.sup ih
  | blowup I hb hperm hsmooth hblowup ι g D hD hgen children ih => exact (Finset.univ.sup ih) + 1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineEtaleControlTree.Construction
