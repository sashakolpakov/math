import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DualFromTranslation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineDifferenceHomogeneity

/-! # Projective Dual -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual ample translation quotient gives dual abelian data over
a Noetherian rational affine base. Difference-line homogeneity is proved
from the projective cube theorem, including on nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineDifferenceHomogeneity.Theta.Geometric

variable {R : Type} [CommRing R] [IsNoetherianRing R] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of R))} {L : Line.Bundles.LineBundle A.scheme.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme}

section

variable (Q : Ample.TranslationQuotient.AmpleTranslationQuotient A L P)
    (qS : Spec (.of R) ⟶ Spec (.of ℚ)) (hL : L.IsAmple)

def Ample.TranslationQuotient.AmpleTranslationQuotient.dualData : Dual.Data.DualAbelianData A :=
  Q.dualData_of_difference qS hL (Noetherian.AffineDifferenceHomogeneity.Theta.Geometric.noetherianAffine_difference_homogeneous A L P)

def Ample.TranslationQuotient.AmpleTranslationQuotient.dualIsogeny : Abelian.Schemes.AbelianScheme.Isogeny A (Q.dualData qS hL).abelian := Q.isogeny

instance Ample.TranslationQuotient.AmpleTranslationQuotient.dualIsogeny_etale : Etale (Q.dualIsogeny qS hL).hom.left := Q.etale

def Ample.TranslationQuotient.AmpleTranslationQuotient.dualPoincareRecovery :
    (((Q.dualData qS hL).poincare).pullback
      ((Q.dualIsogeny qS hL).hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf :=
  Q.descendedDifference_pullbackIso

end

include P in
theorem Rational.ProjectiveDual.rationalProjectiveDual_exists
    (qS : Spec (.of R) ⟶ Spec (.of ℚ)) (hL : L.IsAmple) :
    ∃ (D : Dual.Data.DualAbelianData A) (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian),
      Etale m.hom.left ∧ Nonempty
        ((D.poincare.pullback (m.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
          (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf) := by
  obtain ⟨Q⟩ := Ample.TranslationQuotient.ampleTranslationQuotient_nonempty A L P qS hL
  exact ⟨Q.dualData qS hL, Q.dualIsogeny qS hL, Q.dualIsogeny_etale qS hL,
    ⟨Q.dualPoincareRecovery qS hL⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
