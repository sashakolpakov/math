import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FamilyPoincareCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

/-! # Dual Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical representing dual supplies the dual and Poincare data of a moduli isomorphism once the actual abelian group isomorphism preserves polarization and full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def Moduli.Isomorphisms.LevelPreservingIso.ofCanonicalDual (e : A.abelian.scheme ≅ B.abelian.scheme) [IsMonHom e.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)
    (hp : A.polarization.isogeny.hom ≫ (A.dual.familyComparisonIso B.dual e).hom =
      e.hom ≫ B.polarization.isogeny.hom)
    (hl : ∀ (T : Over S)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (A.level.hom.app (.op T) c).val ≫ e.hom = (B.level.hom.app (.op T) c).val) :
    Moduli.Isomorphisms.LevelPreservingIso A B where
  abelian := e
  dual := A.dual.familyComparisonIso B.dual e
  abelianGroup := inferInstance
  dualGroup := A.dual.familyComparisonIso_isMonHom B.dual e PD PE
  polarization := hp
  poincare := A.dual.familyComparisonIso_poincare B.dual e P
  level := hl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
