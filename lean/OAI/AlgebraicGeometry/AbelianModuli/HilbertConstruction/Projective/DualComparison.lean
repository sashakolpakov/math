import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PointedMapsAreHomomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.RepresentingIsoPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport

/-! # Dual Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Canonical comparisons of projectively presented dual abelian schemes preserve the group law over locally noetherian bases. The comparison also transports along any group isomorphism of the original abelian schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}

theorem Dual.Data.DualAbelianData.uniqueUnderlyingIso_isMonHom (D E : Dual.Data.DualAbelianData A)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation D.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation E.abelian.scheme) :
    IsMonHom (D.uniqueUnderlyingIso E).hom :=
  Projective.PointedMapsAreHomomorphisms.projectivePointedMap_isMonHom D.abelian E.abelian PD PE _ (D.uniqueUnderlyingIso_preserves_unit E)

def Dual.Data.DualAbelianData.familyComparisonIso (D : Dual.Data.DualAbelianData A) (E : Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] : D.abelian.scheme ≅ E.abelian.scheme :=
  (D.familyTransport e).uniqueUnderlyingIso E

omit [IsLocallyNoetherian S] in
theorem Dual.Data.DualAbelianData.familyComparisonIso_preserves_unit (D : Dual.Data.DualAbelianData A) (E : Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    η[D.abelian.scheme] ≫ (D.familyComparisonIso E e).hom = η[E.abelian.scheme] :=
  (D.familyTransport e).uniqueUnderlyingIso_preserves_unit E

theorem Dual.Data.DualAbelianData.familyComparisonIso_isMonHom (D : Dual.Data.DualAbelianData A) (E : Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (PD : Projective.ProjectivePresentations.ProjectivePresentation D.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation E.abelian.scheme) :
    IsMonHom (D.familyComparisonIso E e).hom :=
  (D.familyTransport e).uniqueUnderlyingIso_isMonHom E PD PE

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
