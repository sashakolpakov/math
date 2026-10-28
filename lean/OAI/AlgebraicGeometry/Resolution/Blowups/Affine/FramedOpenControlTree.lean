import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FramedControlTree
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterFiniteFrameCover

/-! # Framed Open Control Tree -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FramedOpenControlTree.Construction

noncomputable section

/-! Finite coordinate-center blowup trees allowing finite affine open refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Every branch uses the same control. Refinement nodes are finite actual
affine open covers; blowup nodes are actual charts of centers with dual
coordinate frames. No existence assertion is built into this type. -/
inductive AffineFramedOpenControlTree (k : Type u) [CommRing k] (b : ℕ) :
    (R : CommRingCat.{u}) → [Algebra k R] → Ideal R → Type (u + 1)
  | terminal {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (hterminal : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (b - 1) = ⊤) :
      AffineFramedOpenControlTree k b R J
  | refineOpen {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (ι : Type u) [Fintype ι] (S : ι → CommRingCat.{u}) [∀ i, Algebra k (S i)]
      (f : ∀ i, R →ₐ[k] S i)
      (hf : ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (f i).toRingHom)))
      (hcover : ∀ p : PrimeSpectrum R, ∃ i, ∃ q : PrimeSpectrum (S i),
        PrimeSpectrum.comap (f i).toRingHom q = p)
      (children : ∀ i, AffineFramedOpenControlTree k b (S i) (J.map (f i).toRingHom)) :
      AffineFramedOpenControlTree k b R J
  | blowup {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (ι : Type u) [Fintype ι] [DecidableEq ι]
      (g : ι → R) (D : ι → Derivation k R R)
      (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
      (hb : 0 < b) (hperm : J ≤ (Ideal.span (Set.range g)) ^ b)
      (children : ∀ i, AffineFramedOpenControlTree k b
        (.of (Blowup.Charts.Construction.blowupChart (Ideal.span (Set.range g)) ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩))
        (ControlledTransform.Construction.blowupControlledTransform (Ideal.span (Set.range g)) J b
          ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩)) :
      AffineFramedOpenControlTree k b R J

/-- Counts blowup depth; passing to an affine open cover does not increase it. -/
def AffineFramedOpenControlTree.blowupDepth {k : Type u} [CommRing k] {b : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
    (T : Construction.AffineFramedOpenControlTree k b R J) : ℕ := by
  classical
  induction T with
  | terminal ht => exact 0
  | refineOpen ι S f hf hcover children ih => exact Finset.univ.sup ih
  | blowup ι g D hD hb hperm children ih => exact (Finset.univ.sup ih) + 1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FramedOpenControlTree.Construction
