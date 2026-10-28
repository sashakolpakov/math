import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CupCommonCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupRefinedPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupMixedBoundary
import OAI.AlgebraicGeometry.Albanese.Construction.Smooth

/-! # Cup Mixed Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CupMixedBoundary

noncomputable section

/-! On an actual complex abelian variety, pull back a cup boundary
along multiplication and the two projections. Their original native
H1 classes give an explicit boundary for the refined mixed rectangle sum. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase)

local instance cupAbelianIntegral : IsIntegral A.scheme.left := IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A
local instance cupAbelianProductIntegral : IsIntegral (A.scheme ⊗ A.scheme).left :=
  Albanese.Construction.Smooth.smooth_tensor_integral A.scheme A.scheme
local instance cupAbelianProductSmooth : Smooth (A.scheme ⊗ A.scheme).hom := by
  change Smooth (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom)
  infer_instance
local instance cupAbelianProductSeparated : IsSeparated (A.scheme ⊗ A.scheme).hom := by
  change IsSeparated (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom)
  infer_instance
local instance cupAbelianDualProductDiagonal :
    IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ (A.scheme ⊗ A.scheme)).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal (A.scheme ⊗ A.scheme)

theorem abelianCup_common_mixedBoundary
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    {I B : Type} [Fintype B] (U : I → A.scheme.left.Opens) (hU : iSup U = ⊤)
    (v w : B → ∀ i j, Γ(A.scheme.left, U i ⊓ U j))
    (hv : ∀ a, RegularPair.Closed.RegularPairCocycle A.scheme.left U (v a))
    (hw : ∀ a, RegularPair.Closed.RegularPairCocycle A.scheme.left U (w a))
    (p : ∀ i j, Γ(A.scheme.left, U i ⊓ U j))
    (hp : Regular.BoundaryShuffle.RegularTripleBoundary A.scheme.left U p
      (fun i j l => ∑ a, RegularPair.CupSymmetry.regularPairCupTriple A.scheme.left U (v a) (w a) i j l)) :
    ∃ q : ∀ i j, Γ((A.scheme ⊗ A.scheme).left,
        CupCommonCover.abelianCupCommonCover A.scheme U i ⊓ CupCommonCover.abelianCupCommonCover A.scheme U j),
      Regular.BoundaryShuffle.RegularTripleBoundary (A.scheme ⊗ A.scheme).left (CupCommonCover.abelianCupCommonCover A.scheme U) q
        (Regular.CupRefinement.regularTripleRefinement (A.scheme ⊗ A.scheme).left
          (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover A.scheme.hom A.scheme.hom U U) (CupCommonCover.abelianCupCommonCover A.scheme U)
          Prod.fst (fun _ => inf_le_left) (fun i j l => ∑ a,
            (RegularPair.CupSymmetry.regularPairCupTriple (A.scheme ⊗ A.scheme).left
              (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover A.scheme.hom A.scheme.hom U U)
              (RectangleCupShuffle.rectangleLeftRegularPair A.scheme.hom A.scheme.hom U U (v a))
              (RectangleCupShuffle.rectangleRightRegularPair A.scheme.hom A.scheme.hom U U (w a)) i j l +
            RegularPair.CupSymmetry.regularPairCupTriple (A.scheme ⊗ A.scheme).left
              (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover A.scheme.hom A.scheme.hom U U)
              (RectangleCupShuffle.rectangleRightRegularPair A.scheme.hom A.scheme.hom U U (v a))
              (RectangleCupShuffle.rectangleLeftRegularPair A.scheme.hom A.scheme.hom U U (w a)) i j l))) := by
  let X := A.scheme
  let Z := X ⊗ X
  let W := CupCommonCover.abelianCupCommonCover X U
  let m : Z ⟶ X := fst X X * snd X X
  let r₀ : (Σ _ : I, I) × I → I := Prod.snd
  let r₁ : (Σ _ : I, I) × I → I := fun a => a.1.1
  let r₂ : (Σ _ : I, I) × I → I := fun a => a.1.2
  have h₀ : ∀ a, W a ≤ m.left ⁻¹ᵁ U (r₀ a) := fun _ => inf_le_right
  have h₁ : ∀ a, W a ≤ (fst X X).left ⁻¹ᵁ U (r₁ a) := fun _ => inf_le_left.trans inf_le_left
  have h₂ : ∀ a, W a ≤ (snd X X).left ⁻¹ᵁ U (r₂ a) := fun _ => inf_le_left.trans inf_le_right
  have hW := CupCommonCover.abelianCupCommonCover_covers X U hU
  let v₀ := fun a => RegularPair.RefinedPullback.regularPairRefinedPullback m U W r₀ h₀ (v a)
  let v₁ := fun a => RegularPair.RefinedPullback.regularPairRefinedPullback (fst X X) U W r₁ h₁ (v a)
  let v₂ := fun a => RegularPair.RefinedPullback.regularPairRefinedPullback (snd X X) U W r₂ h₂ (v a)
  let w₀ := fun a => RegularPair.RefinedPullback.regularPairRefinedPullback m U W r₀ h₀ (w a)
  let w₁ := fun a => RegularPair.RefinedPullback.regularPairRefinedPullback (fst X X) U W r₁ h₁ (w a)
  let w₂ := fun a => RegularPair.RefinedPullback.regularPairRefinedPullback (snd X X) U W r₂ h₂ (w a)
  obtain ⟨q, hq⟩ := Regular.CupMixedBoundary.regularCupMixedBoundary_of_three_boundaries Z.left W hW v₀ v₁ v₂ w₀ w₁ w₂
    (fun a => RegularPair.RefinedPullback.regularPairRefinedPullback_cocycle m U W r₀ h₀ (v a) (hv a))
    (fun a => RegularPair.RefinedPullback.regularPairRefinedPullback_cocycle (fst X X) U W r₁ h₁ (v a) (hv a))
    (fun a => RegularPair.RefinedPullback.regularPairRefinedPullback_cocycle (snd X X) U W r₂ h₂ (v a) (hv a))
    (fun a => RegularPair.RefinedPullback.regularPairRefinedPullback_cocycle m U W r₀ h₀ (w a) (hw a))
    (fun a => RegularPair.RefinedPullback.regularPairRefinedPullback_cocycle (fst X X) U W r₁ h₁ (w a) (hw a))
    (fun a => RegularPair.RefinedPullback.regularPairRefinedPullback_cocycle (snd X X) U W r₂ h₂ (w a) (hw a))
    (fun a => RegularPair.RefinedPullback.regularPairSheafClass_refinedPullback_mul A D P (fst X X) (snd X X)
      U W hU hW r₀ r₁ r₂ h₀ h₁ h₂ (v a) (hv a))
    (fun a => RegularPair.RefinedPullback.regularPairSheafClass_refinedPullback_mul A D P (fst X X) (snd X X)
      U W hU hW r₀ r₁ r₂ h₀ h₁ h₂ (w a) (hw a))
    (RegularPair.RefinedPullback.regularPairRefinedPullback m U W r₀ h₀ p)
    (RegularPair.RefinedPullback.regularPairRefinedPullback (fst X X) U W r₁ h₁ p)
    (RegularPair.RefinedPullback.regularPairRefinedPullback (snd X X) U W r₂ h₂ p)
    (Regular.CupRefinedPullback.regularTripleRefinedPullback_cupSum_boundary m U W r₀ h₀ p v w hp)
    (Regular.CupRefinedPullback.regularTripleRefinedPullback_cupSum_boundary (fst X X) U W r₁ h₁ p v w hp)
    (Regular.CupRefinedPullback.regularTripleRefinedPullback_cupSum_boundary (snd X X) U W r₂ h₂ p v w hp)
  refine ⟨q, ?_⟩
  erw [Regular.RefinementOperations.regularTripleRefinement_sum]
  simpa only [Regular.RefinementOperations.regularTripleRefinement_add, Regular.CupRefinement.regularPairCupTriple_refinement,
    CupCommonCover.abelianCupCommonCover_leftPair, CupCommonCover.abelianCupCommonCover_rightPair] using hq

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CupMixedBoundary
