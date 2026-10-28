import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentChartOverlaps
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.SubschemeDescent

/-! # Containment Global -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobal.GradedHilbert

noncomputable section

/-! Glue the compatible affine native containment loci to an actual
global closed subscheme of the locally noetherian parameter scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (B : Over S) [IsLocallyNoetherian B.left] (n : ℕ)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B)
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B).IdealSheafData)

def nativeContainmentGlueData : Scheme.GlueData := by
  have hOpen : ∀ i : B.left.affineOpenCover.I₀, IsOpenImmersion (B.left.affineOpenCover.f i) :=
    fun i => ContainmentAffineCharts.affineParameterChartInclusion_isOpenImmersion B i
  have hClosed : ∀ i : B.left.affineOpenCover.I₀,
      IsClosedImmersion (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left :=
    fun i => ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion_isClosedImmersion B n F K i
  exact @Closed.CoverGluing.closedCoverGlueData B.left B.left.affineOpenCover.I₀ B.left.affineOpenCover.openCover.X
    (fun i => (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart B n F K i).left) B.left.affineOpenCover.f
    (fun i => (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left)
    hOpen hClosed (ContainmentChartOverlaps.GradedHilbert.nativeContainmentChart_overlap B n F K)

def nativeContainmentGlobalMap : (nativeContainmentGlueData B n F K).glued ⟶ B.left := by
  have hOpen : ∀ i : B.left.affineOpenCover.I₀, IsOpenImmersion (B.left.affineOpenCover.f i) :=
    fun i => ContainmentAffineCharts.affineParameterChartInclusion_isOpenImmersion B i
  have hClosed : ∀ i : B.left.affineOpenCover.I₀,
      IsClosedImmersion (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left :=
    fun i => ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion_isClosedImmersion B n F K i
  exact @Closed.CoverGluing.closedCoverParameter B.left B.left.affineOpenCover.I₀ B.left.affineOpenCover.openCover.X
    (fun i => (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart B n F K i).left) B.left.affineOpenCover.f
    (fun i => (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left)
    hOpen hClosed (ContainmentChartOverlaps.GradedHilbert.nativeContainmentChart_overlap B n F K)

instance nativeContainmentGlobalMap_isClosedImmersion : IsClosedImmersion (nativeContainmentGlobalMap B n F K) := by
  have hClosed : ∀ i : B.left.affineOpenCover.I₀,
      IsClosedImmersion (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left :=
    fun i => ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion_isClosedImmersion B n F K i
  exact @Closed.SubschemeDescent.closedCoverParameter_isClosedImmersion B.left B.left.affineOpenCover.openCover
    (fun i => (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart B n F K i).left)
    (fun i => (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left)
    hClosed (ContainmentChartOverlaps.GradedHilbert.nativeContainmentChart_overlap B n F K)

def nativeContainmentGlobalScheme : Over S := Over.mk (nativeContainmentGlobalMap B n F K ≫ B.hom)

def nativeContainmentGlobalInclusion : nativeContainmentGlobalScheme B n F K ⟶ B :=
  Over.homMk (nativeContainmentGlobalMap B n F K) rfl

instance nativeContainmentGlobalInclusion_isClosedImmersion :
    IsClosedImmersion (nativeContainmentGlobalInclusion B n F K).left :=
  nativeContainmentGlobalMap_isClosedImmersion B n F K

theorem nativeContainmentChart_globalMap (i : B.left.affineOpenCover.I₀) :
    (nativeContainmentGlueData B n F K).ι i ≫ nativeContainmentGlobalMap B n F K =
      (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left ≫ B.left.affineOpenCover.f i := by
  have hOpen : ∀ i : B.left.affineOpenCover.I₀, IsOpenImmersion (B.left.affineOpenCover.f i) :=
    fun i => ContainmentAffineCharts.affineParameterChartInclusion_isOpenImmersion B i
  have hClosed : ∀ i : B.left.affineOpenCover.I₀,
      IsClosedImmersion (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left :=
    fun i => ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion_isClosedImmersion B n F K i
  exact @Closed.CoverGluing.closedCoverChart_parameter B.left B.left.affineOpenCover.I₀ B.left.affineOpenCover.openCover.X
    (fun i => (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart B n F K i).left) B.left.affineOpenCover.f
    (fun i => (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left)
    hOpen hClosed (ContainmentChartOverlaps.GradedHilbert.nativeContainmentChart_overlap B n F K) i

def nativeContainmentChartToGlobal (i : B.left.affineOpenCover.I₀) :
    ContainmentAffineCharts.GradedHilbert.nativeContainmentChart B n F K i ⟶ nativeContainmentGlobalScheme B n F K :=
  Over.homMk ((nativeContainmentGlueData B n F K).ι i)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ B.hom) (nativeContainmentChart_globalMap B n F K i)).trans
        ((Category.assoc _ _ _).trans (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).w)))

instance nativeContainmentChartToGlobal_isOpenImmersion (i : B.left.affineOpenCover.I₀) :
    IsOpenImmersion (nativeContainmentChartToGlobal B n F K i).left :=
  Scheme.GlueData.ι_isOpenImmersion (nativeContainmentGlueData B n F K) i

theorem nativeContainmentChartToGlobal_inclusion (i : B.left.affineOpenCover.I₀) :
    nativeContainmentChartToGlobal B n F K i ≫ nativeContainmentGlobalInclusion B n F K =
      ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i ≫ ContainmentAffineCharts.affineParameterChartInclusion B i :=
  Over.OverMorphism.ext (nativeContainmentChart_globalMap B n F K i)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobal.GradedHilbert
