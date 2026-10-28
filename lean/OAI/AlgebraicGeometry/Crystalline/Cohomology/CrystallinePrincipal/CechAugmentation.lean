import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech

/-! # Cech Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.CechAugmentation.CrystallinePrincipalCechAugmentation

noncomputable section

/-!
# The augmented native principal-frame Čech complex

The proved natural section equivalences give an augmentation from the
original frame-form module. It is a quasi-isomorphism for every finite
unit-ideal cover; no cohomological comparison is required as input.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)
  {ι : Type u} [Finite ι] (s : ι → Q.thickening.ring)

local notation "QR" => Q.thickening.ring

def augmentation :
    (CochainComplex.single₀ (ModuleCat.{u} QR)).obj (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) ⟶
      Cech.CrystallinePrincipalCech.complex p k B σ a Q n s :=
  (CochainComplex.single₀ (ModuleCat.{u} QR)).map
    (tilde.toOpen (R := CommRingCat.of QR) (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) ⊤) ≫
  Cech.Descent.CechDescent.augmentation QR (Affine.Cech.AffineCech.model QR)
    (fun i => Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR (s i))
    (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.associatedSheaf p k B σ Q n).obj ≫
  (Cech.CrystallinePrincipalCech.complexIso p k B σ a Q n s).inv

theorem quasiIso (hs : Ideal.span (Set.range s) = ⊤) :
    QuasiIso (augmentation p k B σ a Q n s) := by
  let t := tilde.toOpen (R := CommRingCat.of QR) (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) ⊤
  have ht : IsIso t := inferInstance
  have ht' : QuasiIso ((CochainComplex.single₀ (ModuleCat.{u} QR)).map t) :=
    HomotopyEquiv.quasiIso_hom (HomotopyEquiv.ofIso
      ((CochainComplex.single₀ (ModuleCat.{u} QR)).mapIso (asIso t)))
  have ha := Affine.Cech.AffineCech.tilde_quasiIso QR s (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) hs
  have he : QuasiIso (Cech.CrystallinePrincipalCech.complexIso p k B σ a Q n s).inv :=
    HomotopyEquiv.quasiIso_hom (HomotopyEquiv.ofIso (Cech.CrystallinePrincipalCech.complexIso p k B σ a Q n s).symm)
  have hi := quasiIso_comp _ _ (hφ := ha) (hφ' := he)
  exact quasiIso_comp _ _ (hφ := ht') (hφ' := hi)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.CechAugmentation.CrystallinePrincipalCechAugmentation
