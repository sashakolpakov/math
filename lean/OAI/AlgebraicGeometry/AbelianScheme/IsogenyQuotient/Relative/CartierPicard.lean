import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierClosedImmersion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.EtaleGroup

/-! # Cartier Picard -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierPicard.Construction

noncomputable section

/-! Construct the quotient of the original canonical Picard dual by
the actual Cartier character subgroup over an unrestricted base.
Identification of this quotient with a new Picard representative is
a subsequent obligation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
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
theorem relativeCartierPicardQuotient_exists :
    ∃ (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian Q)
      (r : Q.scheme ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
      Etale q.hom.left ∧ IsMonHom r ∧
      q.hom ≫ r = (𝟙 (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) ^ n ∧
      r ≫ q.hom = (𝟙 Q.scheme) ^ n ∧
      (∀ (T : Over S) (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
        a ≫ q.hom = 1 ↔ ∃! x : T ⟶ C.dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C = a) ∧
      Descent.Construction.QuotientUniversalProperty (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C) q.hom := by
  have : IsFinite C.dual.X.hom := C.finite
  have : Etale C.dual.X.hom := KilledGroupEtale.Construction.cartierRepresentative_etale_of_killed (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) C n hn hk
  exact Finite.EtaleGroup.Construction.finiteEtaleGroupQuotient_exists (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian C.dual.X
    (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C) (CartierClosedImmersion.Construction.canonicalCartierPicardInclusion_closedImmersion D f C n hn hk)
    n (Canonical.DualData.Construction.canonicalCartierPicardInclusion_pow D f C n hk)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierPicard.Construction
