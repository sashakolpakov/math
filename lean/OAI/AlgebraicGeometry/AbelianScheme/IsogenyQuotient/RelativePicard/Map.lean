import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierPicard
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.FactorGroup

/-! # Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.Map.Construction

noncomputable section

/-! The relative quotient of the original canonical dual carries the
unique group map induced by actual Picard pullback. Its representability
is not assumed or asserted here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : X ⟶ A.scheme) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left] (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
  (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

include hn hk in
set_option backward.isDefEq.respectTransparency false in
theorem relativePicardQuotientMap_exists :
    ∃ (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian Q)
      (r : Q.scheme ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
      (i : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj),
      Etale q.hom.left ∧ IsMonHom r ∧
      q.hom ≫ r = (𝟙 (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) ^ n ∧
      r ≫ q.hom = (𝟙 Q.scheme) ^ n ∧
      (∀ (T : Over S) (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
        a ≫ q.hom = 1 ↔ ∃! x : T ⟶ C.dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C = a) ∧
      Descent.Construction.QuotientUniversalProperty (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C) q.hom ∧
      uliftYoneda.map q.hom ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f ∧
      (∀ T : Over S, i.app (op T) (ULift.up (1 : T ⟶ Q.scheme)) = 1) ∧
      (∀ (T : Over S) (x y : T ⟶ Q.scheme),
        i.app (op T) (ULift.up (x * y)) = i.app (op T) (ULift.up x) * i.app (op T) (ULift.up y)) ∧
      (∀ j : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj,
        uliftYoneda.map q.hom ≫ j = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f → j = i) := by
  obtain ⟨Q, q, r, he, hr, hqr, hrq, hker, hquot⟩ :=
    Relative.CartierPicard.Construction.relativeCartierPicardQuotient_exists D f C n hn hk
  obtain ⟨i, hi, hu⟩ := Factor.Construction.relativePicardQuotientFactor_existsUnique D f C q.hom hker
  exact ⟨Q, q, r, i, he, hr, hqr, hrq, hker, hquot, hi,
    FactorGroup.Construction.relativePicardFactor_one D f q.hom i hi,
    fun _ x y => FactorGroup.Construction.relativePicardFactor_mul D f q.hom i hi x y, hu⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.Map.Construction
