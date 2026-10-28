import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CupAlternatingTensor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.OpenSubcover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.RefinementOperations

/-! # Cover Cup Tensor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.CoverCupTensor.Construction

noncomputable section

/-! An actual cup boundary on the original, possibly infinite, affine
cover of an abelian variety gives the alternating tensor relation for
the original H1 classes. Compactness supplies a finite subcover; all
sections, boundaries, and classes are transported by actual restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance originalCupCohomologyAddGroup {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{0}).obj F))

local instance originalCupSheafH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (CategoryTheory.Sheaf.H (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf Z.left.sheaf) 1) :=
  AbelianModuli.ReferenceFamily.StructureComplexScalars.structureH1ComplexModule Z

local instance originalCoverH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z.left) 1) := AbelianModuli.ReferenceFamily.StructureComplexScalars.structureH1ComplexModule Z

theorem originalCoverCup_alternatingTensor_eq_zero
    {n : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    {I B : Type} [Fintype B]
    (U : I → A.scheme.left.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    (hUU : ∀ i j, IsAffineOpen (U i ⊓ U j))
    (v w : B → ∀ i j, Γ(A.scheme.left, U i ⊓ U j))
    (hv : ∀ a, AbelianModuli.ReferenceFamily.RegularPair.Closed.RegularPairCocycle A.scheme.left U (v a))
    (hw : ∀ a, AbelianModuli.ReferenceFamily.RegularPair.Closed.RegularPairCocycle A.scheme.left U (w a))
    (p : ∀ i j, Γ(A.scheme.left, U i ⊓ U j))
    (hp : AbelianModuli.ReferenceFamily.Regular.BoundaryShuffle.RegularTripleBoundary A.scheme.left U p
      (fun i j l => ∑ a, AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry.regularPairCupTriple A.scheme.left U (v a) (w a) i j l)) :
    ∑ a, (AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (v a) (hv a) ⊗ₜ[ℂ]
      AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (w a) (hw a) -
      AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (w a) (hw a) ⊗ₜ[ℂ]
      AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (v a) (hv a)) = 0 := by
  classical
  let : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  obtain ⟨t, ht⟩ := AbelianModuli.ReferenceFamily.Finite.OpenSubcover.exists_finite_open_subcover U hU
  let V : t → A.scheme.left.Opens := fun i => U i.val
  let r : t → I := Subtype.val
  have hr (i : t) : V i ≤ U (r i) := le_rfl
  let v' := fun a => AbelianModuli.ReferenceFamily.RegularPair.Refinement.regularPairRefinement A.scheme.left U V r hr (v a)
  let w' := fun a => AbelianModuli.ReferenceFamily.RegularPair.Refinement.regularPairRefinement A.scheme.left U V r hr (w a)
  have hv' := fun a => AbelianModuli.ReferenceFamily.RegularPair.Refinement.regularPairRefinement_cocycle A.scheme.left U V r hr (v a) (hv a)
  have hw' := fun a => AbelianModuli.ReferenceFamily.RegularPair.Refinement.regularPairRefinement_cocycle A.scheme.left U V r hr (w a) (hw a)
  have hp' := AbelianModuli.ReferenceFamily.Regular.CupRefinement.regularTripleRefinement_boundary A.scheme.left U V r hr p _ hp
  have he : AbelianModuli.ReferenceFamily.Regular.CupRefinement.regularTripleRefinement A.scheme.left U V r hr
      (fun i j l => ∑ a, AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry.regularPairCupTriple A.scheme.left U (v a) (w a) i j l) =
      fun i j l => ∑ a, AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry.regularPairCupTriple A.scheme.left V (v' a) (w' a) i j l := by
    calc
      _ = (fun i j l => ∑ a, AbelianModuli.ReferenceFamily.Regular.CupRefinement.regularTripleRefinement A.scheme.left U V r hr
          (AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry.regularPairCupTriple A.scheme.left U (v a) (w a)) i j l) := by
        funext i j l
        exact map_sum _ _ _
      _ = _ := by
        funext i j l
        apply Finset.sum_congr rfl
        intro a _
        exact congrFun (congrFun (congrFun
          (AbelianModuli.ReferenceFamily.Regular.CupRefinement.regularPairCupTriple_refinement A.scheme.left U V r hr (v a) (w a)) i) j) l
  rw [he] at hp'
  have H := AbelianModuli.ReferenceFamily.Intrinsic.CupAlternatingTensor.nativeCup_alternatingTensor_eq_zero A D P V ht
    (fun i => hAffine i.val) (fun i j => hUU i.val j.val) v' w' hv' hw'
    (AbelianModuli.ReferenceFamily.RegularPair.Refinement.regularPairRefinement A.scheme.left U V r hr p) hp'
  have hvc (a : B) : AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass A.scheme.left V ht (v' a) (hv' a) =
      AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (v a) (hv a) :=
    AbelianModuli.ReferenceFamily.RegularPair.Refinement.regularPairSheafClass_refinement A.scheme.left U V r hr (v a) hU ht (hv a)
  have hwc (a : B) : AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass A.scheme.left V ht (w' a) (hw' a) =
      AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairSheafClass A.scheme.left U hU (w a) (hw a) :=
    AbelianModuli.ReferenceFamily.RegularPair.Refinement.regularPairSheafClass_refinement A.scheme.left U V r hr (w a) hU ht (hw a)
  simp only [hvc, hwc] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.CoverCupTensor.Construction
