import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualOpenChartCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames

/-! # Frame Cech Class -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameCechClass.Construction

noncomputable section

/-! The original infinitesimal Picard class of two equally reduced
line pullbacks is computed by their actual native affine charts.
The first-order cochain uses the original frame transition sections;
its closedness and native H1 comparison are proved, not assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsAffineHom (pullback.diagonal (terminal.from (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left))]
    {M : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Modules} {I : Type}
    (s : I → AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) (hs : ∀ i, IsAffineOpen (s i).domain)

/-- Pull the actual transition section to its native affine coefficient
scheme, take its first-order coefficient, and transport on the original
reduced intersection. -/
def nativeFrameCechCochain :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf).obj
      (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) 1 :=
  fun a =>
    let V := fun i => (s i).domain
    let W := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a
    let u := (s (a 0)).transition (s (a 1)) W
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 1)
    (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechIntersection X V a)).toRingHom
      (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap (R := Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X W).left, ⊤))
        (S := Γ(X.left, (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ W))
        ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ W).topIso.hom.hom
        ((Scheme.ΓSpecIso (.of (DualNumber Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X W).left, ⊤)))).hom.hom
          ((DualOpenChartCoefficients.Construction.nativeDualOpenCoefficientChart X W (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualCechIntersection_affine X V hs a)).appTop.hom
            ((show (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens from W).topIso.inv.hom u.val))))).snd

theorem nativeFrameCechCochain_eq :
    nativeFrameCechCochain X s hs =
      AbelianModuli.ReferenceFamily.Dual.UnitCechCoefficients.dualUnitCechAdditive X.left.sheaf.obj (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain))
        (AbelianModuli.ReferenceFamily.LineFrameDualCech.lineFrameDualCech X s hs) := by
  funext a
  exact congrArg TrivSqZeroExt.snd
    (DualOpenChartCoefficients.Construction.nativeDualCechChart_coefficients X (fun i => (s i).domain) hs a
      ((s (a 0)).transition (s (a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1)).val)

variable [LocallyOfFiniteType X.hom] [IsReduced X.left]

theorem nativeFrameCechCochain_closed
    (hn : AbelianModuli.ReferenceFamily.Dual.UnitCechCoefficients.DualUnitCechNormalized X.left.sheaf.obj
      (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) (AbelianModuli.ReferenceFamily.LineFrameDualCech.lineFrameDualCech X s hs)) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf).obj
      (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) 1 (nativeFrameCechCochain X s hs) = 0 := by
  rw [nativeFrameCechCochain_eq]
  exact AbelianModuli.ReferenceFamily.Dual.UnitCechCoefficients.dualUnitCechAdditive_closed X.left.sheaf.obj
    (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) (AbelianModuli.ReferenceFamily.LineFrameDualCech.lineFrameDualCech X s hs) hn
    (AbelianModuli.ReferenceFamily.LineFrameDualCech.lineFrameDualCech_cocycle X s hs)

/-- For the actual difference of two equally reduced pullbacks, the
native chart cochain is closed and represents the original Picard H1
class. Normalization and the common frame cover are constructed. -/
theorem dualLinePullbackDifferenceClass_eq_nativeFrameCech
    {Y : Scheme.{0}} (f g : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (h : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ f =
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g)
    [IsAffineHom g] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) {J : Type}
    (t : J → AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf) (ha : ∀ j, IsAffineOpen (t j).domain)
    (hc : iSup (fun j => (t j).domain) = ⊤) :
    ∃ (hcover : iSup (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain)) = ⊤)
      (hclosed : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf).obj
        (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain)) 1
        (nativeFrameCechCochain X (fun j => AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L (t j))
          (fun j => (ha j).preimage g)) = 0),
      AbelianModuli.ReferenceFamily.DualLine.PullbackDifference.dualLinePullbackDifferenceClass X f g h L =
        DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechCover X (fun j => g ⁻¹ᵁ (t j).domain))
          (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf) hcover 0
          (nativeFrameCechCochain X (fun j => AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L (t j))
            (fun j => (ha j).preimage g)) hclosed := by
  obtain ⟨hcover, hn, he⟩ := AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualLinePullbackDifferenceClass_eq_openFrames X f g h L t ha hc
  refine ⟨hcover, nativeFrameCechCochain_closed X
    (fun j => AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L (t j)) (fun j => (ha j).preimage g) hn, ?_⟩
  simp only [nativeFrameCechCochain_eq]
  simp only [AbelianModuli.ReferenceFamily.Regular.DualUnitClass.regularDualUnitClass, AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.dualUnitCechClass] at he
  exact he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FrameCechClass.Construction
