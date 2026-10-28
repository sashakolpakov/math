import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.TranslationKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroPicardEquationBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.UnramifiedFieldCriterion
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationZeroBaseChange
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeEtaleCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Translation Kernel Etale -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.TranslationKernelEtale

noncomputable section

/-! The actual translation kernel of an ample line on a projective
abelian scheme is etale over a Noetherian affine rational base.
Geometric kernels give unramifiedness; the original local Picard
equations and the H1 bound give flatness over the full base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric

variable {S : Scheme} [hS : IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (qS : S ⟶ Spec (.of ℚ)) (A : Abelian.Schemes.AbelianScheme g S)
    (L : Line.Bundles.LineBundle A.scheme.left) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

local instance rationalKernelSource_locallyNoetherian : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

include hS

theorem ampleTranslationKernel_geometric_isFinite (hL : L.IsAmple)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S) :
    IsFinite ((Over.pullback b).obj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P)).hom := by
  let A' := A.pullback b
  let L' := L.pullback (pullback.fst A.scheme.hom b)
  let P' := P.baseChange b
  let Z' := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A' L' P'
  let : IsAffineHom (pullback.fst A.scheme.hom b) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback A.scheme.hom b).flip (inferInstanceAs (IsAffineHom b))
  have hL' : L'.IsAmple := hL.pullback_of_isAffineHom (pullback.fst A.scheme.hom b)
  let : IsFinite Z'.hom := Geometric.TranslationKernel.geometricTranslationKernel_isFinite A' L' P' hL'
  obtain ⟨e₀, _⟩ := Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric.exists_translationZero_baseChange_iso A L P b P'
  let e : (Over.pullback b).obj (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) ≅ Z' := e₀
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map e.hom))
  have h : IsFinite (e.hom.left ≫ Z'.hom) := inferInstance
  exact e.hom.w ▸ h

include qS

theorem rationalTranslationKernel_formallyUnramified (hL : L.IsAmple) :
    FormallyUnramified (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let : LocallyOfFiniteType Z.hom :=
    Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroSchemeOver_locallyOfFiniteType P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  apply Geometric.UnramifiedFieldCriterion.formallyUnramified_of_geometricFieldPullbacks Z.hom
  intro k _ _ b
  let : CharZero k := CharZeroFibers.charZero_of_rational_scheme_map (b ≫ qS)
  let A' := A.pullback b
  let L' := L.pullback (pullback.fst A.scheme.hom b)
  let P' := P.baseChange b
  let Z' := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A' L' P'
  let : IsAffineHom (pullback.fst A.scheme.hom b) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback A.scheme.hom b).flip (inferInstanceAs (IsAffineHom b))
  have hL' : L'.IsAmple := hL.pullback_of_isAffineHom (pullback.fst A.scheme.hom b)
  let : Etale Z'.hom := Geometric.TranslationKernel.geometricTranslationKernel_etale A' L' P' hL'
  obtain ⟨e₀, _⟩ := Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric.exists_translationZero_baseChange_iso A L P b P'
  let e : (Over.pullback b).obj Z ≅ Z' := e₀
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map e.hom))
  have h : FormallyUnramified (e.hom.left ≫ Z'.hom) := inferInstance
  change FormallyUnramified ((Over.pullback b).obj Z).hom
  exact e.hom.w ▸ h

theorem rationalTranslationKernel_etale (hL : L.IsAmple) :
    Etale (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P).hom := by
  let : FormallyUnramified
      ((Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) P).hom ≫ A.scheme.hom) :=
    rationalTranslationKernel_formallyUnramified qS A L P hL
  exact Picard.ThetaConstruction.RelativeEtaleCriterion.Geometric.RelativeRigidifiedCharts.zeroProjection_etale P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
    g A.scheme.hom (fun z =>
      ZeroPicardEquationBound.rationalFamily_zero_stalk_H1_le_dimension qS A P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) z)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.TranslationKernelEtale
