import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.UniversalIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FamilyPoincareCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange

/-! # Universal Dual Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.UniversalDualIsomorphism

noncomputable section

/-! The bounded abelian-isomorphism parameter carries a canonical universal dual isomorphism. Projective presentations of the duals prove that it preserves the group law, and a projective presentation of the target proves Poincare compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g n : ℕ}
variable {A B : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A) (E : Dual.Data.DualAbelianData B)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def boundedAbelianUniversalDualIso :
    (D.abelian.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).scheme ≅
      (E.abelian.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).scheme := by
  have := UniversalIso.boundedAbelianUniversalIso_isMonHom A B j P
  exact (D.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).familyComparisonIso
    (E.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom) (UniversalIso.boundedAbelianUniversalIso A B j P)

theorem boundedAbelianUniversalDualIso_isMonHom
    (PD : Projective.ProjectivePresentations.ProjectivePresentation D.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation E.abelian.scheme) :
    IsMonHom (boundedAbelianUniversalDualIso D E j P).hom := by
  have : IsNoetherian (IsoParameters.boundedAbelianIsoParameter A B j P).left :=
    (IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A B j P).noetherian
  have := UniversalIso.boundedAbelianUniversalIso_isMonHom A B j P
  exact (D.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).familyComparisonIso_isMonHom
    (E.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom) (UniversalIso.boundedAbelianUniversalIso A B j P)
    (PD.baseChange _) (PE.baseChange _)

theorem boundedAbelianUniversalDualIso_poincare (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme) :
    Line.Bundles.LineBundle.pullbackClass
      ((boundedAbelianUniversalDualIso D E j P).hom ⊗ₘ (UniversalIso.boundedAbelianUniversalIso A B j P).hom).left
      (Line.Bundles.LineBundle.classOf (E.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).poincare) =
      Line.Bundles.LineBundle.classOf (D.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).poincare := by
  have : IsNoetherian (IsoParameters.boundedAbelianIsoParameter A B j P).left :=
    (IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A B j P).noetherian
  have := UniversalIso.boundedAbelianUniversalIso_isMonHom A B j P
  exact (D.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).familyComparisonIso_poincare
    (E.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom) (UniversalIso.boundedAbelianUniversalIso A B j P) (PB.baseChange _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.UniversalDualIsomorphism
