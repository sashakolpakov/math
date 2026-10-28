import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BoundaryAuxiliaryOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineEtaleControlTree

/-! # Control Phase Tree -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ControlPhaseTree.Construction

noncomputable section

/-! Actual finite boundary-intersection phases with separate marked and boundary transforms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- A boundary phase retains the selected intersection at control one,
the original ideal at its prescribed control, and their exact auxiliary
identity. At terminal leaves the selected intersection misses the entire
remaining marked order locus. -/
inductive BoundaryControlPhaseTree (k : Type u) [CommRing k] (m : ℕ) :
    (R : CommRingCat.{u}) → [Algebra k R] → Ideal R → Ideal R → Type (u + 1)
  | terminal {R : CommRingCat.{u}} [Algebra k R] {J L : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L 1 = ⊤)
      (hclear : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m - 1) ⊔ L = ⊤) :
      BoundaryControlPhaseTree k m R J L
  | refineEtale {R : CommRingCat.{u}} [Algebra k R] {J L : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L 1 = ⊤)
      (ι : Type u) [Fintype ι] (S : ι → CommRingCat.{u}) [∀ i, Algebra k (S i)]
      (f : ∀ i, R →ₐ[k] S i) (hf : ∀ i, (f i).toRingHom.Etale)
      (hcover : ∀ p : PrimeSpectrum R, ∃ i, ∃ q : PrimeSpectrum (S i),
        PrimeSpectrum.comap (f i).toRingHom q = p)
      (children : ∀ i, BoundaryControlPhaseTree k m (S i)
        (J.map (f i).toRingHom) (L.map (f i).toRingHom)) : BoundaryControlPhaseTree k m R J L
  | blowup {R : CommRingCat.{u}} [Algebra k R] {J L : Ideal R}
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L 1 = ⊤)
      (I : Ideal R) (hJ : J ≤ I ^ m) (hL : L ≤ I)
      (hfactor : ∀ a : I, ControlledTransform.Construction.blowupControlledTransform I (AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m) m a =
        AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal (ControlledTransform.Construction.blowupControlledTransform I J m a) (ControlledTransform.Construction.blowupControlledTransform I L 1 a) m)
      (hsmooth : Algebra.Smooth k (R ⧸ I))
      (hblowup : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (ι : Type u) [Fintype ι] [DecidableEq ι] (g : ι → I) (D : ι → Derivation k R R)
      (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
      (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I)
      (children : ∀ i, BoundaryControlPhaseTree k m (.of (Blowup.Charts.Construction.blowupChart I (g i)))
        (ControlledTransform.Construction.blowupControlledTransform I J m (g i)) (ControlledTransform.Construction.blowupControlledTransform I L 1 (g i))) :
      BoundaryControlPhaseTree k m R J L

def BoundaryControlPhaseTree.blowupDepth {k : Type u} [CommRing k] {m : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {J L : Ideal R}
    (T : Construction.BoundaryControlPhaseTree k m R J L) : ℕ := by
  classical
  induction T with
  | terminal hbound hclear => exact 0
  | refineEtale hbound ι S f hf hcover children ih => exact Finset.univ.sup ih
  | blowup hbound I hJ hL hfactor hsmooth hblowup ι g D hD hgen children ih =>
      exact (Finset.univ.sup ih) + 1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ControlPhaseTree.Construction
