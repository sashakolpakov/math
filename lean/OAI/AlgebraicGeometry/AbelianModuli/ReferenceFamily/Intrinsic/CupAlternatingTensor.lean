import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CupMixedBoundary
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleMixedCupSum

/-! # Cup Alternating Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CupAlternatingTensor

noncomputable section

/-! A finite cup boundary on a projective complex abelian variety
forces zero alternating tensor of the original structure-sheaf H1
classes. The proof uses actual pullbacks, refinement, and affine
rectangle detection, with no assumed native cup comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance alternatingCohomologyAddGroup {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{0}).obj F))

local instance alternatingSheafH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf Z.left.sheaf) 1) :=
  StructureComplexScalars.structureH1ComplexModule Z

local instance cupAlternatingH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule Z.left) 1) := StructureComplexScalars.structureH1ComplexModule Z

theorem nativeCup_alternatingTensor_eq_zero
    {n : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    {I B : Type} [Fintype I] [DecidableEq I] [Fintype B]
    (U : I → A.scheme.left.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    (hUU : ∀ i j, IsAffineOpen (U i ⊓ U j))
    (v w : B → ∀ i j, Γ(A.scheme.left, U i ⊓ U j))
    (hv : ∀ a, RegularPair.Closed.RegularPairCocycle A.scheme.left U (v a))
    (hw : ∀ a, RegularPair.Closed.RegularPairCocycle A.scheme.left U (w a))
    (p : ∀ i j, Γ(A.scheme.left, U i ⊓ U j))
    (hp : Regular.BoundaryShuffle.RegularTripleBoundary A.scheme.left U p
      (fun i j l => ∑ a, RegularPair.CupSymmetry.regularPairCupTriple A.scheme.left U (v a) (w a) i j l)) :
    ∑ a, (RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (v a) (hv a) ⊗ₜ[ℂ]
      RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (w a) (hw a) -
      RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (w a) (hw a) ⊗ₜ[ℂ]
      RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (v a) (hv a)) = 0 := by
  let X := A.scheme
  let Z := X ⊗ X
  let R := Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom X.hom U U
  let W := Abelian.CupCommonCover.abelianCupCommonCover X U
  have hR := RectangleClassDetection.rectangleOpenCover_covers X.hom X.hom U U hU hU
  have hW := Abelian.CupCommonCover.abelianCupCommonCover_covers X U hU
  have : IsSeparated Z.hom := by
    change IsSeparated (pullback.fst X.hom X.hom ≫ X.hom)
    infer_instance
  have ht : IsSeparated (Z.hom ≫ terminal.from Foundations.Scheme.ProjectiveSpace.complexBase) := inferInstance
  have he : Z.hom ≫ terminal.from Foundations.Scheme.ProjectiveSpace.complexBase = terminal.from Z.left := Subsingleton.elim _ _
  have : (pullback X.hom X.hom).IsSeparated := ⟨he ▸ ht⟩
  let c : RectangleBoundaryShuffle.rectangleOrdinaryCech2 X.hom X.hom U U := fun i j l => ∑ a,
    (RegularPair.CupSymmetry.regularPairCupTriple Z.left R (RectangleCupShuffle.rectangleLeftRegularPair X.hom X.hom U U (v a))
      (RectangleCupShuffle.rectangleRightRegularPair X.hom X.hom U U (w a)) i j l +
    RegularPair.CupSymmetry.regularPairCupTriple Z.left R (RectangleCupShuffle.rectangleRightRegularPair X.hom X.hom U U (v a))
      (RectangleCupShuffle.rectangleLeftRegularPair X.hom X.hom U U (w a)) i j l)
  have hc : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf Z.left.sheaf).obj R 2
      (Regular.BoundaryShuffle.regularTripleCechCochain Z.left R c) = 0 :=
    Regular.TripleSumCocycles.regularPairMixedCupSum_cech_closed Z.left R _ _ _ _
      (fun a => RectangleCupShuffle.rectangleLeftRegularPair_cocycle X.hom X.hom U U (v a) (hv a))
      (fun a => RectangleCupShuffle.rectangleRightRegularPair_cocycle X.hom X.hom U U (w a) (hw a))
      (fun a => RectangleCupShuffle.rectangleRightRegularPair_cocycle X.hom X.hom U U (v a) (hv a))
      (fun a => RectangleCupShuffle.rectangleLeftRegularPair_cocycle X.hom X.hom U U (w a) (hw a))
  obtain ⟨q, hq⟩ := Abelian.CupMixedBoundary.abelianCup_common_mixedBoundary A D P U hU v w hv hw p hp
  have hz := Regular.RefinementOperations.regularTripleSheafClass_zero_of_refinement_boundary Z.left R W Prod.fst
    (fun _ => inf_le_left) hR hW c hc q hq
  have hd := RectangleDetector.nativeRectangleMixedProjection_zero_of_sheafClass_zero X X U U hU hU hUU hUU
    hAffine hAffine c hc hz
  exact (RectangleMixedCupSum.nativeRectangleMixedProjection_mixedCupSum X X U U hU hU hUU hUU
    v w v w hv hw hv hw).symm.trans hd

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CupAlternatingTensor
