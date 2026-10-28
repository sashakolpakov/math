import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.AnalytificationFree
import OAI.AlgebraicGeometry.Betti.SmoothDimension

/-! # Standard Smooth Exterior Rank -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothExteriorRank

noncomputable section

section

/-! Standard smooth algebraic exterior frames have the binomial rank of the native complex manifold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [IsAffine X.left]
  [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra X)]

theorem standardSmooth_globalCoordinate_dimension :
    Algebra.IsStandardSmoothOfRelativeDimension (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra X) := by
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨Classical.arbitrary X.left, trivial⟩⟩
  have hs : RingHom.IsStandardSmooth (X.hom.appLE ⊤ ⊤ le_top).hom := by
    apply (RingHom.isStandardSmooth_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (X.hom.appLE ⊤ ⊤ le_top)).mp
    exact inferInstanceAs (Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra X))
  have hd := Betti.SmoothDimension.Realization.affineStandardSmooth_dimension X.hom ⊤ (isAffineOpen_top X.left) hs
  exact Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra_standardSmooth
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) X.hom ⊤ hd

theorem standardSmooth_exteriorFrameIndex_card (n : ℕ) :
    Nat.card (Smooth.ExteriorFrames.exteriorFrameIndex X n) = (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom).choose n := by
  let : IsDomain (Affine.ExteriorRestrictions.globalCoordinateAlgebra X) := inferInstanceAs (IsDomain Γ(X.left, ⊤))
  let : Algebra.IsStandardSmoothOfRelativeDimension
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra X) :=
    standardSmooth_globalCoordinate_dimension X
  change Nat.card (Set.powersetCard
    (Module.Free.ChooseBasisIndex (Affine.ExteriorRestrictions.globalCoordinateAlgebra X) Ω[Affine.ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ]) n) = _
  rw [Set.powersetCard.card]
  have hcard := (Module.finrank_eq_nat_card_basis
    (Module.Free.chooseBasis (Affine.ExteriorRestrictions.globalCoordinateAlgebra X) Ω[Affine.ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ])).symm
  have hd := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := ℂ) (S := Affine.ExteriorRestrictions.globalCoordinateAlgebra X) (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
  exact congrArg (fun k => k.choose n) (hcard.trans hd)

end

/-! Actual exterior frames on a nonempty standard smooth open have the ambient scheme's native rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] (U : X.left.Opens) [Nonempty U]
  [IsAffine (Open.AffineIsoEvaluation.openOver X U).left]
  [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U))]

theorem standardSmooth_openCoordinate_dimension :
    Algebra.IsStandardSmoothOfRelativeDimension (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) := by
  let : Algebra.IsStandardSmooth ℂ Γ(X.left, U) :=
    Algebra.IsStandardSmooth.of_algEquiv (StandardSmoothBasis.openSectionTopAlgEquiv X U).symm
  have hs : RingHom.IsStandardSmooth (X.hom.appLE ⊤ U le_top).hom := by
    apply (RingHom.isStandardSmooth_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (X.hom.appLE ⊤ U le_top)).mp
    exact inferInstanceAs (Algebra.IsStandardSmooth ℂ Γ(X.left, U))
  have hd := Betti.SmoothDimension.Realization.affineStandardSmooth_dimension X.hom U
    (inferInstanceAs (IsAffine (Open.AffineIsoEvaluation.openOver X U).left)) hs
  let : Algebra.IsStandardSmoothOfRelativeDimension
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) ℂ Γ(X.left, U) :=
    Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra_standardSmooth
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) X.hom U hd
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) (StandardSmoothBasis.openSectionTopAlgEquiv X U)

theorem standardSmooth_openExteriorFrameIndex_card (n : ℕ) :
    Nat.card (Smooth.ExteriorFrames.exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X U) n) =
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom).choose n := by
  let : Nontrivial (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) :=
    Function.Injective.nontrivial (StandardSmoothBasis.openSectionTopAlgEquiv X U).injective
  let : Algebra.IsStandardSmoothOfRelativeDimension
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) :=
    standardSmooth_openCoordinate_dimension X U
  change Nat.card (Set.powersetCard (Module.Free.ChooseBasisIndex
    (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) Ω[Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)⁄ℂ]) n) = _
  rw [Set.powersetCard.card]
  have hc := (Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis
    (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) Ω[Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)⁄ℂ])).symm
  have hd := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := ℂ) (S := Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U))
        (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
  exact congrArg (fun k => k.choose n) (hc.trans hd)

end

end OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothExteriorRank
