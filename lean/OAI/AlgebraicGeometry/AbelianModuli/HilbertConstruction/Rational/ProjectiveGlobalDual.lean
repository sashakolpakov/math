import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedPicardDifferenceIsogeny
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectiveDual
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineGluing

/-! # Projective Global Dual -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectiveGlobalDual

noncomputable section

/-! An original dual abelian scheme for a projective abelian family over
any locally Noetherian rational base. The local quotients use the native
pullbacks of the presentation's O(1) bundle. Their represented Picard
sheaves glue, and the original global difference line supplies Poincare
normalization by effective quotient descent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}

namespace RationalProjectiveGlobalDual

variable (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
  (qS : S ⟶ Spec (.of ℚ))

local instance chart_noetherian (i : S.affineOpenCover.I₀) :
    IsNoetherianRing (S.affineOpenCover.X i) := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian S i

def chartLine (i : S.affineOpenCover.I₀) :
    Line.Bundles.LineBundle (A.pullback (S.affineOpenCover.f i)).scheme.left :=
  P.ampleLineBundle.pullback (pullback.fst A.scheme.hom (S.affineOpenCover.f i))

omit [IsLocallyNoetherian S] in
theorem chartLine_isAmple (i : S.affineOpenCover.I₀) : (chartLine A P i).IsAmple :=
  (P.baseChange (S.affineOpenCover.f i)).ampleLineBundle_isAmple.of_iso
    (P.baseChangeTwistingBundleIso (S.affineOpenCover.f i))

def chartQuotient (i : S.affineOpenCover.I₀) :
    Ample.TranslationQuotient.AmpleTranslationQuotient (A.pullback (S.affineOpenCover.f i))
      (chartLine A P i) (P.baseChange (S.affineOpenCover.f i)) :=
  (Ample.TranslationQuotient.ampleTranslationQuotient_nonempty (A.pullback (S.affineOpenCover.f i))
    (chartLine A P i) (P.baseChange (S.affineOpenCover.f i))
    (S.affineOpenCover.f i ≫ qS) (chartLine_isAmple A P i)).some

def chartDual (i : S.affineOpenCover.I₀) :
    Dual.Data.DualAbelianData (A.pullback (S.affineOpenCover.f i)) := by
  exact @Ample.TranslationQuotient.AmpleTranslationQuotient.dualData
    (S.affineOpenCover.X i) (S.affineOpenCover.X i).commRing
    (chart_noetherian (S := S) i) g
    (A.pullback (S.affineOpenCover.f i)) (chartLine A P i)
    (P.baseChange (S.affineOpenCover.f i)) (chartQuotient A P qS i)
    (S.affineOpenCover.f i ≫ qS) (chartLine_isAmple A P i)

def chartInducingIsogeny (i : S.affineOpenCover.I₀) :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (S.affineOpenCover.f i)) (chartDual A P qS i).abelian := by
  exact @Ample.TranslationQuotient.AmpleTranslationQuotient.dualIsogeny
    (S.affineOpenCover.X i) (S.affineOpenCover.X i).commRing
    (chart_noetherian (S := S) i) g
    (A.pullback (S.affineOpenCover.f i)) (chartLine A P i)
    (P.baseChange (S.affineOpenCover.f i)) (chartQuotient A P qS i)
    (S.affineOpenCover.f i ≫ qS) (chartLine_isAmple A P i)

instance chartInducingIsogeny_etale (i : S.affineOpenCover.I₀) :
    Etale (chartInducingIsogeny A P qS i).hom.left := by
  exact @Ample.TranslationQuotient.AmpleTranslationQuotient.dualIsogeny_etale
    (S.affineOpenCover.X i) (S.affineOpenCover.X i).commRing
    (chart_noetherian (S := S) i) g
    (A.pullback (S.affineOpenCover.f i)) (chartLine A P i)
    (P.baseChange (S.affineOpenCover.f i)) (chartQuotient A P qS i)
    (S.affineOpenCover.f i ≫ qS) (chartLine_isAmple A P i)

def chartRecovery (i : S.affineOpenCover.I₀) :
    (((chartDual A P qS i).poincare).pullback
      ((chartInducingIsogeny A P qS i).hom ⊗ₘ
        𝟙 (A.pullback (S.affineOpenCover.f i)).scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (A.pullback (S.affineOpenCover.f i)) (chartLine A P i)).sheaf := by
  exact @Ample.TranslationQuotient.AmpleTranslationQuotient.dualPoincareRecovery
    (S.affineOpenCover.X i) (S.affineOpenCover.X i).commRing
    (chart_noetherian (S := S) i) g
    (A.pullback (S.affineOpenCover.f i)) (chartLine A P i)
    (P.baseChange (S.affineOpenCover.f i)) (chartQuotient A P qS i)
    (S.affineOpenCover.f i ≫ qS) (chartLine_isAmple A P i)

def inducingCharts : GluedPicardDifferenceIsogeny.DualOpenGluing.DifferenceIsogenyCharts A S.affineOpenCover.openCover
    (chartDual A P qS) P P.ampleLineBundle where
  isogeny := chartInducingIsogeny A P qS
  etale := chartInducingIsogeny_etale A P qS
  classifies i := by
    let : IsLocallyNoetherian (Spec (S.affineOpenCover.X i)) :=
      isLocallyNoetherian_Spec.mpr (chart_noetherian (S := S) i)
    exact (chartDual A P qS i).differenceMap_class_of_recovery (chartLine A P i)
      (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous (A.pullback (S.affineOpenCover.f i))
        (P.baseChange (S.affineOpenCover.f i)) (chartLine A P i))
      (chartInducingIsogeny A P qS i).hom (chartRecovery A P qS i)

/-- Actual original dual data, including the represented homogeneous
Picard sheaf and the normalized Poincare line. -/
def dualData : Dual.Data.DualAbelianData A :=
  GluedPicardDifferenceIsogeny.DualOpenGluing.dualData A S.affineOpenCover.openCover (chartDual A P qS)
    P P.ampleLineBundle (inducingCharts A P qS)

/-- The global translation isogeny induced by the presentation's O(1). -/
def inducingIsogeny : Abelian.Schemes.AbelianScheme.Isogeny A (dualData A P qS).abelian :=
  GluedPicardDifferenceIsogeny.DualOpenGluing.inducingIsogeny A S.affineOpenCover.openCover (chartDual A P qS)
    P P.ampleLineBundle (inducingCharts A P qS)

instance inducingIsogeny_etale : Etale (inducingIsogeny A P qS).hom.left :=
  GluedPicardDifferenceIsogeny.DualOpenGluing.inducingIsogeny_etale A S.affineOpenCover.openCover (chartDual A P qS)
    P P.ampleLineBundle (inducingCharts A P qS)

/-- The Poincare bundle recovers the actual global original difference
bundle, with no choice of a different projective family. -/
def poincareRecovery :
    (((dualData A P qS).poincare).pullback
      ((inducingIsogeny A P qS).hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A P.ampleLineBundle).sheaf :=
  GluedPicardDifferenceIsogeny.DualOpenGluing.poincareRecovery A S.affineOpenCover.openCover (chartDual A P qS)
    P P.ampleLineBundle (inducingCharts A P qS)

end RationalProjectiveGlobalDual

theorem rationalLocallyNoetherianProjectiveDual_exists
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (qS : S ⟶ Spec (.of ℚ)) :
    ∃ (D : Dual.Data.DualAbelianData A) (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian),
      Etale m.hom.left ∧ Nonempty
        ((D.poincare.pullback (m.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
          (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A P.ampleLineBundle).sheaf) :=
  ⟨RationalProjectiveGlobalDual.dualData A P qS,
    RationalProjectiveGlobalDual.inducingIsogeny A P qS,
    RationalProjectiveGlobalDual.inducingIsogeny_etale A P qS,
    ⟨RationalProjectiveGlobalDual.poincareRecovery A P qS⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectiveGlobalDual
