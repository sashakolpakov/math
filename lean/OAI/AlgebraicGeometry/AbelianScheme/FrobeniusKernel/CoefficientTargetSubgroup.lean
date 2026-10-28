import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HigherProjectorOnBlock

/-! # Coefficient Target Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientTargetSubgroup.Construction

noncomputable section

/-! A subgroup of a level-one coefficient block retains its actual
abelian inclusion, q-torsion bound, and every higher projector's fixed equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (τ : Gal(E/ℚ)) {J : Grp (Over S)}
  (i : J ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp)

def coefficientTargetInclusion : J ⟶ Grp.mk B.scheme :=
  Grp.homMk (i.hom.hom ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ)

theorem coefficientTargetInclusion_closed [IsClosedImmersion i.hom.hom.left] :
    IsClosedImmersion (coefficientTargetInclusion j iota hsplit B σ τ i).hom.hom.left := by
  have : IsClosedImmersion (CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ).left :=
    inferInstanceAs (IsClosedImmersion
      (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion B σ (q ^ 1) (j.projector iota hsplit 1 τ)).left)
  exact inferInstanceAs (IsClosedImmersion (i.hom.hom.left ≫ (CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ).left))

theorem coefficientTargetInclusion_killed :
    (coefficientTargetInclusion j iota hsplit B σ τ i).hom.hom ^ q = 1 := by
  change (i.hom.hom ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ) ^ q = 1
  have h := (PELModuli.CMPoints.BlocksProjectors.splitBlockSchemePointsEquiv j iota hsplit B σ 1 τ J.X i.hom.hom).property.1
  change (i.hom.hom ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ) ^ (q ^ 1) = 1 at h
  simpa only [pow_one] using h

theorem coefficientTargetInclusion_fixed (n : ℕ) :
    (coefficientTargetInclusion j iota hsplit B σ τ i).hom.hom ≫
      σ.map (j.projector iota hsplit (n + 1) τ) =
      (coefficientTargetInclusion j iota hsplit B σ τ i).hom.hom :=
  HigherProjectorOnBlock.Construction.levelOneBlock_fixed_by_higherProjector j iota hsplit B σ n τ J.X i.hom.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientTargetSubgroup.Construction
