import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedDeRham
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TruncatedSections

/-! # Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Naturality.IntrinsicCechGeometricNaturality

noncomputable section

/-! The native Čech–de Rham comparison commutes with actual geometric pullback using a constructed map of refined resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  {X Y : Over (Spec (CommRingCat.of R))} [IsSeparated X.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
  {ι κ : Type} [Finite ι] [Finite κ]
  (U : ι → Y.left.Opens) (V : κ → X.left.Opens) (r : κ → ι)
  (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

def sectionsMap : TruncatedSections.IntrinsicCechHodgeComparison.sections R Y U ⟶ TruncatedSections.IntrinsicCechHodgeComparison.sections R X V :=
  Intrinsic.SectionComplexPullback.IntrinsicSectionComplexPullback.map f
    (PullbackTotal.IntrinsicCechPullback.integerMap f U V r hr (DeRham.Int.sheafPullback f))

theorem naturality (hU : ∀ i, IsAffineOpen (U i)) (hcoverU : iSup U = ⊤)
    (hV : ∀ i, IsAffineOpen (V i)) (hcoverV : iSup V = ⊤)
    (n : ℕ) (x : (TruncatedSections.IntrinsicCechHodgeComparison.sections R Y U).homology (n : ℤ)) :
    TruncatedSections.IntrinsicCechHodgeComparison.equiv R X V hV hcoverV n
      (HomologicalComplex.homologyMap (sectionsMap R f U V r hr) (n : ℤ) x) =
      DeRham.Int.pullback f n (TruncatedSections.IntrinsicCechHodgeComparison.equiv R Y U hU hcoverU n x) := by
  let s : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y ⟶
      Resolution.IntrinsicCechResolution.integerTotal R Y.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) :=
    Resolution.IntrinsicCechResolution.integerEdge R Y.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)
  let t : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X ⟶
      Resolution.IntrinsicCechResolution.integerTotal R X.left V (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
    Resolution.IntrinsicCechResolution.integerEdge R X.left V (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
  have : QuasiIso s := Resolution.IntrinsicCechResolution.integerEdge_quasiIso R Y.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) hcoverU
  have : QuasiIso t := Resolution.IntrinsicCechResolution.integerEdge_quasiIso R X.left V (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) hcoverV
  exact Intrinsic.ResolvedDeRham.IntrinsicResolvedPullback.deRham_naturality f s t
    (PullbackTotal.IntrinsicCechPullback.integerMap f U V r hr (DeRham.Int.sheafPullback f))
    (PullbackTotal.IntrinsicCechPullback.integerAugmentation f U V r hr (DeRham.Int.sheafPullback f)) 0 0
    (TotalAcyclic.IntrinsicCechTotalAcyclic.integerTotal_ext_subsingleton R Y U hU)
    (TotalAcyclic.IntrinsicCechTotalAcyclic.integerTotal_ext_subsingleton R X V hV) n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Naturality.IntrinsicCechGeometricNaturality
