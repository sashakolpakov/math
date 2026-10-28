import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.PersistentCoefficientStep

/-! # Framed Control Tree -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FramedControlTree.Construction

noncomputable section

/-! Finite actual blowup trees with smooth centers or finite dual-coordinate frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- A finite tree of actual blowup charts at a fixed control. Each node
records a finite generating cover, a permissible smooth center, and smoothness
of the entire actual blowup. The leaves have empty controlled order locus. -/
inductive SmoothAffineControlTree (k : Type u) [CommRing k] (b : ℕ) :
    (R : CommRingCat.{u}) → [Algebra k R] → Ideal R → Type (u + 1)
  | terminal {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (hterminal : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (b - 1) = ⊤) :
      SmoothAffineControlTree k b R J
  | blowup {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (I : Ideal R) (hb : 0 < b) (hperm : J ≤ I ^ b)
      (hsmooth : Algebra.Smooth k (R ⧸ I))
      (hblowup : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (ι : Type u) [Fintype ι] (g : ι → I)
      (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I)
      (children : ∀ i, SmoothAffineControlTree k b (.of (Blowup.Charts.Construction.blowupChart I (g i)))
        (ControlledTransform.Construction.blowupControlledTransform I J b (g i))) :
      SmoothAffineControlTree k b R J

/-- A finite coefficient-resolution tree whose centers carry explicit dual
coordinate derivations. This is input data, not an assertion that such trees
exist for all ideals. -/
inductive AffineFramedControlTree (k : Type u) [CommRing k] (b : ℕ) :
    (H : CommRingCat.{u}) → [Algebra k H] → Ideal H → Type (u + 1)
  | terminal {H : CommRingCat.{u}} [Algebra k H] {C : Ideal H}
      (hterminal : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C (b - 1) = ⊤) :
      AffineFramedControlTree k b H C
  | blowup {H : CommRingCat.{u}} [Algebra k H] {C : Ideal H}
      (ι : Type u) [Fintype ι] [DecidableEq ι]
      (g : ι → H) (δ : ι → Derivation k H H)
      (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0)
      (hb : 0 < b) (hperm : C ≤ (Ideal.span (Set.range g)) ^ b)
      (children : ∀ i, AffineFramedControlTree k b
        (.of (Blowup.Charts.Construction.blowupChart (Ideal.span (Set.range g)) ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩))
        (ControlledTransform.Construction.blowupControlledTransform (Ideal.span (Set.range g)) C b
          ⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩)) :
      AffineFramedControlTree k b H C

def SmoothAffineControlTree.height {k : Type u} [CommRing k] {b : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
    (T : Construction.SmoothAffineControlTree k b R J) : ℕ := by
  classical
  induction T with
  | terminal ht => exact 0
  | blowup I hb hperm hsmooth hblowup ι g hgen children ih =>
      exact (Finset.univ.sup ih) + 1

def AffineFramedControlTree.height {k : Type u} [CommRing k] {b : ℕ}
    {H : CommRingCat.{u}} [Algebra k H] {C : Ideal H}
    (T : Construction.AffineFramedControlTree k b H C) : ℕ := by
  classical
  induction T with
  | terminal ht => exact 0
  | blowup ι g δ hδ hb hperm children ih => exact (Finset.univ.sup ih) + 1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FramedControlTree.Construction
