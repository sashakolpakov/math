import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Factor

/-! # Factor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.Factor.Construction

noncomputable section

/-! Actual Picard pullback descends uniquely through the quotient of
the original dual by its Cartier character subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] (f : X ⟶ A.scheme) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  {Q : Over S} [GrpObj Q]
  (q : (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme ⟶ Q) [IsMonHom q]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
  (hk : ∀ (T : Over S) (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
    a ≫ q = 1 ↔ ∃! x : T ⟶ C.dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C = a)

include hk in
omit [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalPicardPullback_fibre_invariance (T : Over S)
    (a b : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) (h : a ≫ q = b ≫ q) :
    Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T a = Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T b := by
  have hab : (a / b) ≫ q = 1 := by
    change (IsMonHom.monoidHom q T) (a / b) = 1
    rw [map_div]
    change (a ≫ q) / (b ≫ q) = 1
    rw [h]
    exact div_self' _
  obtain ⟨x, hx, _⟩ := (hk T (a / b)).mp hab
  have hz := Canonical.PicardPullback.Construction.canonicalPicardPullbackHom_cartier D f C T x
  rw [hx, map_div] at hz
  exact div_eq_one.mp hz

include hk in
theorem relativePicardQuotientFactor_existsUnique :
    ∃! i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj,
      uliftYoneda.map q ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f := by
  apply Sheaf.Factor.Construction.existsUnique_sheaf_factor_of_fibre_invariance q (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X)
    (Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f)
  intro T a b h
  exact canonicalPicardPullback_fibre_invariance D f C q hk T a b h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.Factor.Construction
