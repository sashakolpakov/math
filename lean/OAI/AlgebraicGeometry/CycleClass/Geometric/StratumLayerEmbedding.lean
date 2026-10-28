import OAI.AlgebraicGeometry.CycleClass.Geometric.AnalyticSupportFiltration
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumSeparation

/-! # Stratum Layer Embedding -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.StratumLayerEmbedding.IntegralSmoothGeometricStratification

noncomputable section

/-!
# Actual smooth pieces as closed embeddings in filtration complements

Every layer of the finite analytic support filtration is the image of its
original smooth integral scheme piece. Restricting the target to the open
complement of the preceding stage makes that actual point map a closed
embedding. Its complex and real differentials are the native immersion
differentials in the inherited open charts.

Only the ambient smooth scheme and the original smooth pieces receive
manifold structures. No manifold structure is assumed on a singular support.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {S : Set X}
variable (Q : IntegralSmoothStratification.IntegralSmoothGeometricStratification f S)

/-- The actual open complement of the stage immediately preceding a layer. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationComplement (i : Fin Q.analyticSupportList.length) :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) :=
  ⟨(Q.analyticClosedFiltration i.castSucc : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))ᶜ,
    (Q.analyticClosedFiltration i.castSucc).isClosed.isOpen_compl⟩

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationComplement_coe (i : Fin Q.analyticSupportList.length) :
    (Q.analyticFiltrationComplement i : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) =
      (Q.analyticClosedFiltration i.castSucc : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))ᶜ := rfl

/-- The point map of the original piece lands in the next stage and avoids
the preceding stage. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationPiece_map_mem_layer (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Q.analyticFiltrationPiece i).toAmbient x ∈
      (Q.analyticClosedFiltration i.succ : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) \
        (Q.analyticClosedFiltration i.castSucc : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) := by
  rw [Q.analyticClosedFiltration_layer_eq_range i]
  exact Set.mem_range_self x

/-- The unchanged native point map, with codomain restricted to the actual
open complement of the previous filtration stage. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerInclusion (i : Fin Q.analyticSupportList.length) :
    (Q.analyticFiltrationPiece i).analyticSpace → Q.analyticFiltrationComplement i :=
  fun x => ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Q.analyticFiltrationPiece i).toAmbient x,
    (Q.analyticFiltrationPiece_map_mem_layer i x).2⟩

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerInclusion_val (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    (Q.analyticFiltrationLayerInclusion i x).val =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Q.analyticFiltrationPiece i).toAmbient x := rfl

/-- The restricted map still has exactly its original algebraic point map. -/
@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.underlying_analyticFiltrationLayerInclusion (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (Q.analyticFiltrationLayerInclusion i x).val =
      (Q.analyticFiltrationPiece i).toAmbient.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_map (Q.analyticFiltrationPiece i).toAmbient x

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.continuous_analyticFiltrationLayerInclusion (i : Fin Q.analyticSupportList.length) :
    Continuous (Q.analyticFiltrationLayerInclusion i) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Q.analyticFiltrationPiece i).toAmbient).subtype_mk _

/-- The image is precisely the next relative closed-support layer, as a
subset of the open complement with its genuine subspace topology. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.range_analyticFiltrationLayerInclusion (i : Fin Q.analyticSupportList.length) :
    Set.range (Q.analyticFiltrationLayerInclusion i) =
      ClosedSupportFiltration.Cycles.closedSupportLayer (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))
        (Q.analyticClosedFiltration i.castSucc) (Q.analyticClosedFiltration i.succ) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (Q.analyticFiltrationPiece_map_mem_layer i x).1
  · intro hy
    have hr : y.val ∈
        (Q.analyticClosedFiltration i.succ : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) \
          (Q.analyticClosedFiltration i.castSucc : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f))) :=
      ⟨hy, y.property⟩
    rw [Q.analyticClosedFiltration_layer_eq_range i] at hr
    obtain ⟨x, hx⟩ := hr
    exact ⟨x, Subtype.ext hx⟩

/-- The actual smooth piece embeds closedly in the complement of the
preceding closed stage. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.isClosedEmbedding_analyticFiltrationLayerInclusion
    (i : Fin Q.analyticSupportList.length) :
    Topology.IsClosedEmbedding (Q.analyticFiltrationLayerInclusion i) := by
  let : IsImmersion (Q.analyticFiltrationPiece i).toAmbient.left :=
    (Q.analyticFiltrationPiece i).immersion
  refine ⟨?_, ?_⟩
  · exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion
      (Q.analyticFiltrationPiece i).toAmbient).codRestrict
        (Q.analyticFiltrationComplement i : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))
        (fun x => (Q.analyticFiltrationPiece_map_mem_layer i x).2)
  · rw [Q.range_analyticFiltrationLayerInclusion i]
    exact ClosedSupportFiltration.Cycles.closedSupportLayer_isClosed
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))
      (Q.analyticClosedFiltration i.castSucc) (Q.analyticClosedFiltration i.succ)

/-- The smooth source and the literal relative layer are homeomorphic. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerHomeomorph (i : Fin Q.analyticSupportList.length) :
    (Q.analyticFiltrationPiece i).analyticSpace ≃ₜ
      ClosedSupportFiltration.Cycles.closedSupportLayer (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))
        (Q.analyticClosedFiltration i.castSucc) (Q.analyticClosedFiltration i.succ) :=
  (Q.isClosedEmbedding_analyticFiltrationLayerInclusion i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (Q.range_analyticFiltrationLayerInclusion i))

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerHomeomorph_val (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    (Q.analyticFiltrationLayerHomeomorph i x).val = Q.analyticFiltrationLayerInclusion i x := rfl

variable [IsIntegral X] [Smooth f]

local instance : IsIntegral (Over.mk f).left := ‹IsIntegral X›
local instance : Smooth (Over.mk f).hom := ‹Smooth f›
local instance (i : Fin Q.analyticSupportList.length) :
    IsIntegral (Q.analyticFiltrationPiece i).toOver.left :=
  (Q.analyticFiltrationPiece i).integral
local instance (i : Fin Q.analyticSupportList.length) :
    Smooth (Q.analyticFiltrationPiece i).toOver.hom :=
  (Q.analyticFiltrationPiece i).smooth
local instance (i : Fin Q.analyticSupportList.length) :
    IsImmersion (Q.analyticFiltrationPiece i).toAmbient.left :=
  (Q.analyticFiltrationPiece i).immersion

local notation "AmbientModel" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension f) → ℂ)

local instance : ChartedSpace AmbientModel (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk f) ‹IsIntegral X› ‹Smooth f›

/-- The restricted native point map is analytic in the inherited complex
charts, and therefore smooth of every order. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.contMDiff_analyticFiltrationLayerInclusion
    (i : Fin Q.analyticSupportList.length) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, (Q.analyticFiltrationPiece i).analyticModel)) (𝓘(ℂ, AmbientModel)) r
      (Q.analyticFiltrationLayerInclusion i) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (Q.analyticFiltrationComplement i)
    (Q.analyticFiltrationLayerInclusion i) r).mp
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (Q.analyticFiltrationPiece i).toAmbient r

/-- The same map has all orders of real smoothness. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.real_contMDiff_analyticFiltrationLayerInclusion
    (i : Fin Q.analyticSupportList.length) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, (Q.analyticFiltrationPiece i).analyticModel)) (𝓘(ℝ, AmbientModel)) r
      (Q.analyticFiltrationLayerInclusion i) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (Q.analyticFiltrationComplement i)
    (Q.analyticFiltrationLayerInclusion i) r).mp
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (Q.analyticFiltrationPiece i).toAmbient r

/-- Open codomain restriction preserves the actual native complex derivative. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.mfderiv_analyticFiltrationLayerInclusion_eq_ambient
    (i : Fin Q.analyticSupportList.length) (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    (show (Q.analyticFiltrationPiece i).analyticModel →L[ℂ] AmbientModel from
      mfderiv (𝓘(ℂ, (Q.analyticFiltrationPiece i).analyticModel)) (𝓘(ℂ, AmbientModel))
        (Q.analyticFiltrationLayerInclusion i) x) =
    (show (Q.analyticFiltrationPiece i).analyticModel →L[ℂ] AmbientModel from
      mfderiv (𝓘(ℂ, (Q.analyticFiltrationPiece i).analyticModel)) (𝓘(ℂ, AmbientModel))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Q.analyticFiltrationPiece i).toAmbient) x) :=
  ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (Q.analyticFiltrationComplement i)
    (Q.analyticFiltrationLayerInclusion i) x

/-- Open codomain restriction also preserves the actual real derivative. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.real_mfderiv_analyticFiltrationLayerInclusion_eq_ambient
    (i : Fin Q.analyticSupportList.length) (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    (show (Q.analyticFiltrationPiece i).analyticModel →L[ℝ] AmbientModel from
      mfderiv (𝓘(ℝ, (Q.analyticFiltrationPiece i).analyticModel)) (𝓘(ℝ, AmbientModel))
        (Q.analyticFiltrationLayerInclusion i) x) =
    (show (Q.analyticFiltrationPiece i).analyticModel →L[ℝ] AmbientModel from
      mfderiv (𝓘(ℝ, (Q.analyticFiltrationPiece i).analyticModel)) (𝓘(ℝ, AmbientModel))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Q.analyticFiltrationPiece i).toAmbient) x) :=
  ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (Q.analyticFiltrationComplement i)
    (Q.analyticFiltrationLayerInclusion i) x

/-- The closed layer embedding has injective complex differential. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.mfderiv_analyticFiltrationLayerInclusion_injective
    (i : Fin Q.analyticSupportList.length) (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    Function.Injective
      (mfderiv (𝓘(ℂ, (Q.analyticFiltrationPiece i).analyticModel)) (𝓘(ℂ, AmbientModel))
        (Q.analyticFiltrationLayerInclusion i) x) := by
  exact (congrArg (fun L : (Q.analyticFiltrationPiece i).analyticModel →L[ℂ] AmbientModel =>
    Function.Injective L) (Q.mfderiv_analyticFiltrationLayerInclusion_eq_ambient i x)).mpr
      (ComplexPoints.Analytic.IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective (Q.analyticFiltrationPiece i).toAmbient x)

/-- The closed layer embedding has injective real differential as well. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.real_mfderiv_analyticFiltrationLayerInclusion_injective
    (i : Fin Q.analyticSupportList.length) (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    Function.Injective
      (mfderiv (𝓘(ℝ, (Q.analyticFiltrationPiece i).analyticModel)) (𝓘(ℝ, AmbientModel))
        (Q.analyticFiltrationLayerInclusion i) x) := by
  exact (congrArg (fun L : (Q.analyticFiltrationPiece i).analyticModel →L[ℝ] AmbientModel =>
    Function.Injective L) (Q.real_mfderiv_analyticFiltrationLayerInclusion_eq_ambient i x)).mpr
      (ComplexPoints.Analytic.IntrinsicSmoothImmersion.real_mfderiv_nativeScheme_immersion_injective
        (Q.analyticFiltrationPiece i).toAmbient x)

/-- The source model has the dimension computed from the actual piece's
function field; restriction of the ambient target changes no dimensions. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayer_complexDimension_le
    (i : Fin Q.analyticSupportList.length) :
    (Q.analyticFiltrationPiece i).complexDimension ≤
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension f :=
  ((Q.analyticFiltrationPiece i).complexDimension_le).trans_eq
    (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension f)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.StratumLayerEmbedding.IntegralSmoothGeometricStratification
