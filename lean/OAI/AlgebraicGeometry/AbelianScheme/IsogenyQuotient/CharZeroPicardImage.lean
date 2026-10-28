import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ZeroPicardKernelExactness
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.Map
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Image

/-! # Char Zero Picard Image -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharZeroPicardImage.Construction

noncomputable section

/-! The Cartier quotient is an actual abelian Picard image over any
scheme over a characteristic-zero field. Its degree conditions are
derived locally, not supplied as extra hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
  {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : X ⟶ A.scheme) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left] (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

section Factor
variable {Q : Over S} [GrpObj Q] [IsCommMonObj Q] [IsProper Q.hom]
  (q : (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme ⟶ Q) [IsMonHom q]
  (hkill : Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C ≫ q = 1)
  (hk : ∀ (T : Over S) (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
    a ≫ q = 1 ↔ ∃! x : T ⟶ C.dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C = a)

include p hkill hk in
set_option backward.isDefEq.respectTransparency false in
theorem charZeroPicardPullback_fibres_iff (T : Over S)
    (a b : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) :
    Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T a = Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T b ↔ a ≫ q = b ≫ q := by
  constructor
  · intro h
    have hz : Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T (a / b) = 1 := by
      rw [map_div, h]
      exact div_self' _
    have hq := ZeroPicardKernelExactness.Construction.charZeroPicardPullback_kernel_quotient_zero D f C q hkill p T (a / b) hz
    change (IsMonHom.monoidHom q T) (a / b) = 1 at hq
    rw [map_div] at hq
    exact div_eq_one.mp hq
  · exact RelativePicard.Factor.Construction.canonicalPicardPullback_fibre_invariance D f C q hk T a b

variable [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

include p hkill hk in
theorem charZeroPicardQuotientFactor_mono
    (i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj)
    (hi : uliftYoneda.map q ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f) : Mono i := by
  obtain ⟨j, hj, hfac⟩ := Sheaf.Image.Construction.exists_mono_sheaf_factor_of_fibres q (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X)
    (Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f) (charZeroPicardPullback_fibres_iff p D f C q hkill hk)
  obtain ⟨v, _, hu⟩ := RelativePicard.Factor.Construction.relativePicardQuotientFactor_existsUnique D f C q hk
  have hji : j = i := (hu j hfac).trans (hu i hi).symm
  rw [← hji]
  exact hj
end Factor

include p in
set_option backward.isDefEq.respectTransparency false in
theorem charZeroCartierPicardImage_exists (n : ℕ) (hn : 0 < n)
    (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    ∃ (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian Q)
      (r : Q.scheme ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
      (i : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj),
      Etale q.hom.left ∧ IsMonHom r ∧ Mono i ∧
      q.hom ≫ r = (𝟙 (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) ^ n ∧
      r ≫ q.hom = (𝟙 Q.scheme) ^ n ∧
      (∀ (T : Over S) (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
        a ≫ q.hom = 1 ↔ ∃! x : T ⟶ C.dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C = a) ∧
      Descent.Construction.QuotientUniversalProperty (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C) q.hom ∧
      uliftYoneda.map q.hom ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f ∧
      (∀ T : Over S, i.app (op T) (ULift.up (1 : T ⟶ Q.scheme)) = 1) ∧
      (∀ (T : Over S) (x y : T ⟶ Q.scheme),
        i.app (op T) (ULift.up (x * y)) = i.app (op T) (ULift.up x) * i.app (op T) (ULift.up y)) := by
  have hunit := Relative.DegreeBaseChange.Construction.positiveNat_isUnit_on_charZero_field_scheme p n hn
  obtain ⟨Q, q, r, i, he, hr, hqr, hrq, hker, hquot, hfac, h1, hm, _⟩ :=
    RelativePicard.Map.Construction.relativePicardQuotientMap_exists D f C n hunit hk
  have : Mono (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C) :=
    Relative.CartierMonomorphism.Construction.cartierToPicard_mono_of_invertible_kernel_exponent f (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) C n hunit hk
  have hkill : Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C ≫ q.hom = 1 := by
    apply (hker C.dual.X (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C)).mpr
    refine ⟨𝟙 C.dual.X, Category.id_comp _, ?_⟩
    intro x hx
    exact (cancel_mono (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C)).mp
      (hx.trans (Category.id_comp _).symm)
  exact ⟨Q, q, r, i, he, hr, charZeroPicardQuotientFactor_mono p D f C q.hom hkill hker i hfac,
    hqr, hrq, hker, hquot, hfac, h1, hm⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharZeroPicardImage.Construction
