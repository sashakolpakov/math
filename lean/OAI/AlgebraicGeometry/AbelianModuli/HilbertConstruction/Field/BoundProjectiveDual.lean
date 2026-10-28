import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.BoundPicardRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmpleTranslationGeometricPicard
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectiveDual
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KilledTranslationKernelQuotient

/-! # Bound Projective Dual -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual ample translation quotient represents the homogeneous
Picard sheaf on every test scheme when the field H1 bound is supplied.
An invertible exponent annihilating the original kernel constructs that
quotient without a rational-base map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmpleTranslationGeometricPicard.Theta.Geometric

variable {R : Type} [CommRing R] [IsNoetherianRing R] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of R))} {L : Line.Bundles.LineBundle A.scheme.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme}

section

variable (Q : Ample.TranslationQuotient.AmpleTranslationQuotient A L P)
    (hH1 : A.HasFieldStructureH1Bound) (hL : L.IsAmple)

include hH1 hL in
theorem Ample.TranslationQuotient.AmpleTranslationQuotient.fieldBoundHomogeneousParameterMap_isIso :
    IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A Q.descendedDifference.bundle
      (Q.descendedDifference_homogeneous_of_difference
        (Noetherian.AffineDifferenceHomogeneity.Theta.Geometric.noetherianAffine_difference_homogeneous A L P))) :=
  Field.BoundPicardRepresentation.fieldBoundHomogeneousParameterMap_isIso A Q.target P hH1
    Q.descendedDifference
    (Q.descendedDifference_homogeneous_of_difference
      (Noetherian.AffineDifferenceHomogeneity.Theta.Geometric.noetherianAffine_difference_homogeneous A L P))
    Q.descendedDifference_value_injective
    (fun _ _ _ f x => Q.descendedDifference_geometric_surjective_algebraic hL f x)

def Ample.TranslationQuotient.AmpleTranslationQuotient.fieldBoundDualData : Dual.Data.DualAbelianData A := by
  let hδ := Q.descendedDifference_homogeneous_of_difference
    (Noetherian.AffineDifferenceHomogeneity.Theta.Geometric.noetherianAffine_difference_homogeneous A L P)
  have : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A Q.descendedDifference.bundle hδ) :=
    Q.fieldBoundHomogeneousParameterMap_isIso hH1 hL
  exact RepresentationTheory.Theta.Geometric.Dual.PicardData.dualDataOfHomogeneousParameterIso A Q.target Q.descendedDifference.bundle hδ
    Q.descendedDifference.axis Q.descendedDifference_secondAxis

def Ample.TranslationQuotient.AmpleTranslationQuotient.fieldBoundDualIsogeny : Abelian.Schemes.AbelianScheme.Isogeny A (Q.fieldBoundDualData hH1 hL).abelian :=
  Q.isogeny

instance Ample.TranslationQuotient.AmpleTranslationQuotient.fieldBoundDualIsogeny_etale : Etale (Q.fieldBoundDualIsogeny hH1 hL).hom.left := Q.etale

def Ample.TranslationQuotient.AmpleTranslationQuotient.fieldBoundDualPoincareRecovery :
    (((Q.fieldBoundDualData hH1 hL).poincare).pullback
      ((Q.fieldBoundDualIsogeny hH1 hL).hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf :=
  Q.descendedDifference_pullbackIso

end

theorem Field.BoundProjectiveDual.fieldBoundTranslationKernel_etale
    {S : Scheme} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (hH1 : A.HasFieldStructureH1Bound)
    [FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom] :
    Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  have : IsLocallyNoetherian A.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  have : FormallyUnramified
      ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P).hom ≫
        A.scheme.hom) :=
    inferInstanceAs (FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom)
  exact Picard.ThetaConstruction.RelativeEtaleCriterion.Geometric.RelativeRigidifiedCharts.zeroProjection_etale P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
    g A.scheme.hom (fun z => Field.StructurePicardBound.fieldBound_zero_stalk_H1_le_dimension A P hH1
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) z)

theorem Field.BoundProjectiveDual.fieldBoundProjectiveDual_exists_of_killed
    (hH1 : A.HasFieldStructureH1Bound) (hL : L.IsAmple)
    (n : ℕ) (hn : 0 < n)
    (hunit : ∀ x : Spec (.of R), IsUnit (n : (Spec (.of R)).presheaf.stalk x))
    (hi : Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P ^ n = 1) :
    ∃ (D : Dual.Data.DualAbelianData A) (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian),
      Etale m.hom.left ∧ Nonempty
        ((D.poincare.pullback (m.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
          (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf) := by
  have : FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom :=
    KilledTranslationKernelQuotient.killedTranslationKernel_formallyUnramified A L P n hunit hi
  have : Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom :=
    Field.BoundProjectiveDual.fieldBoundTranslationKernel_etale A L P hH1
  obtain ⟨Q⟩ := KilledTranslationKernelQuotient.ampleTranslationQuotient_nonempty_of_killed A L P n hn hunit hi
  exact ⟨Q.fieldBoundDualData hH1 hL, Q.fieldBoundDualIsogeny hH1 hL,
    Q.fieldBoundDualIsogeny_etale hH1 hL, ⟨Q.fieldBoundDualPoincareRecovery hH1 hL⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
