import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactAnalyticOpen
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSmooth
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization
import Mathlib.Topology.Connected.Clopen

/-! # Quasi Projective Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuasiProjectiveComponents

noncomputable section

/-! Compact connected analytic opens in the smooth locus of the actual
quasi-projective moduli scheme are actual projective open-and-closed
subschemes. The construction retains their inclusion in the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Set

def nativeQuasiProjectiveImmersion {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation X) :
    X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.projective.dimension) :=
  Q.embedding ≫ (Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation Q.projective).toOverHom

instance nativeQuasiProjectiveImmersion_isImmersion {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation X) :
    IsImmersion (nativeQuasiProjectiveImmersion Q).left :=
  inferInstanceAs (IsImmersion (Q.embedding.left ≫
    (Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation Q.projective).embedding))

theorem exists_integral_smooth_open_containing_connected_set
    (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [NoetherianSpace Y.left] [LocallyOfFiniteType Y.hom]
    (V : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (hV : IsConnected V)
    (hsmooth : ∀ x ∈ V, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ Y.hom.smoothLocus) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Y.hom,
      IsOpenImmersion R.inclusion ∧
        V ⊆ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Over.homMk R.inclusion rfl : R.toOver ⟶ Y)) := by
  let U := Y.hom.smoothLocus
  have : Smooth (U.ι ≫ Y.hom) := EtaleSmooth.EtaleSmoothLocus.smooth_on_smoothLocus Y.hom
  have : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hV
  let g : V → U.toScheme := fun x => ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val, hsmooth x.val x.property⟩
  have hg : Continuous g :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying.comp continuous_subtype_val).subtype_mk _
  obtain ⟨x, hx⟩ := hV.nonempty
  let y := g ⟨x, hx⟩
  let C := irreducibleComponent y
  have hC : C ∈ irreducibleComponents U.toScheme := irreducibleComponent_mem_irreducibleComponents y
  have hCo : IsOpen C := Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains
    (Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain (U.ι ≫ Y.hom))
    NoetherianSpace.finite_irreducibleComponents hC
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hVC : range g ⊆ C := (isConnected_range hg).isPreconnected.subset_isClopen
    ⟨hCc, hCo⟩ ⟨y, ⟨⟨x, hx⟩, rfl⟩, mem_irreducibleComponent⟩
  let W : U.toScheme.Opens := ⟨C, hCo⟩
  have : IrreducibleSpace W.toScheme := isIrreducible_iff_irreducibleSpace.mp hC.1
  have : IsReduced U.toScheme := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (U.ι ≫ Y.hom)
  have : IsIntegral W.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Y.hom := {
    carrier := W.toScheme
    inclusion := W.ι ≫ U.ι
    immersion := inferInstance
    smooth := by rw [Category.assoc]; infer_instance
    integral := inferInstance }
  have hj : IsOpenImmersion R.inclusion := inferInstanceAs (IsOpenImmersion (W.ι ≫ U.ι))
  refine ⟨R, hj, ?_⟩
  let j : R.toOver ⟶ Y := Over.homMk R.inclusion rfl
  have : IsOpenImmersion j.left := hj
  intro z hz
  change z ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion]
  exact ⟨⟨g ⟨z, hz⟩, hVC ⟨⟨z, hz⟩, rfl⟩⟩, rfl⟩

theorem exists_projective_open_piece_of_compact_connected_analytic_open
    {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Y.hom] (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation Y)
    (V : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (hopen : IsOpen V) (hcompact : IsCompact V)
    (hconnected : IsConnected V)
    (hsmooth : ∀ x ∈ V, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ Y.hom.smoothLocus) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Y.hom,
      IsOpenImmersion R.inclusion ∧ IsClosedImmersion R.inclusion ∧
        Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation R.carrier (R.inclusion ≫ Y.hom)) ∧
        range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Over.homMk R.inclusion rfl : R.toOver ⟶ Y)) = V := by
  have : LocallyOfFiniteType Y.hom := Q.locallyFiniteType
  have : IsNoetherian Y.left := Q.noetherian
  have : IsSeparated Y.hom := Q.separated
  obtain ⟨R, hj, hsub⟩ := exists_integral_smooth_open_containing_connected_set Y V hconnected hsmooth
  let j : R.toOver ⟶ Y := Over.homMk R.inclusion rfl
  have : IsOpenImmersion R.inclusion := hj
  have : IsOpenImmersion j.left := hj
  have : IsIntegral R.toOver.left := R.integral
  have : Smooth R.toOver.hom := R.smooth
  let U : Opens R.analyticSpace := ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j ⁻¹' V,
    hopen.preimage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map j)⟩
  have himage : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j '' (U : Set R.analyticSpace) = V :=
    image_preimage_eq_of_subset hsub
  have hUn : Nonempty U := by
    obtain ⟨x, hx⟩ := hconnected.nonempty
    obtain ⟨z, hz⟩ := hsub hx
    exact ⟨⟨z, show ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j z ∈ V from hz.symm ▸ hx⟩⟩
  let : Nonempty U := hUn
  have hUc : IsCompact (U : Set R.analyticSpace) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j).isEmbedding.isCompact_iff.mpr
      (himage.symm ▸ hcompact)
  let : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  let f := j ≫ nativeQuasiProjectiveImmersion Q
  have : IsImmersion f.left := inferInstanceAs
    (IsImmersion (j.left ≫ (nativeQuasiProjectiveImmersion Q).left))
  let P := CompactAnalyticOpen.projectivePresentation_of_compact_analyticOpen f U
  have hu : (U : Set R.analyticSpace) = univ :=
    CompactAnalyticOpen.compact_analyticOpen_eq_univ_of_projective_immersion f U
  have hrange : range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) = V := by
    simpa only [hu, image_univ] using himage
  have : IsProper (R.inclusion ≫ Y.hom) := P.isProper
  have : IsProper R.inclusion := IsProper.of_comp R.inclusion Y.hom
  have hc : IsClosedImmersion R.inclusion := by
    apply IsClosedImmersion.of_isPreimmersion
    exact R.inclusion.isClosedMap.isClosed_range
  exact ⟨R, hj, hc, ⟨P⟩, hrange⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuasiProjectiveComponents
