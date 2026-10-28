import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.IntrinsicFiniteSurjective

/-! # Graph Base Range -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphBaseRange.Constructions

noncomputable section

/-! The first-coordinate image of each actual normalized divisor graph is
exactly the original image-cycle support on its retained ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.IntrinsicFiniteSurjective.Constructions.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ GraphOpen.Constructions.goodAmbient V W z)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {d : ℕ} (e : AffineCoordinates.Constructions.coverSource V W z U → Fin d → ℂ)

theorem divisorLocalGraph_firstRange :
    Set.range (Prod.fst ∘ EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U e) =
      Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (Image.Constructions.imageCycleSupport V W z) U (hU.trans (GraphOpen.Constructions.goodAmbient_regular V W z))) := by
  rw [← GraphOpen.Constructions.targetAmbientMap_range V W z U hU]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Etale.coverMap V W z) x.val, rfl⟩
  · rintro ⟨t, ht⟩
    obtain ⟨x, hx⟩ := Integral.IntrinsicFiniteSurjective.Constructions.Intrinsic.nativeMap_surjective (Open.Constructions.Etale.coverMap V W z) (Open.Constructions.Etale.coverMap_genericPoint V W z) t
    have hxy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.targetAmbientMap V W z)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Etale.coverMap V W z) x) = y.val := (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.targetAmbientMap V W z)) hx).trans ht
    have hxU : EtaleGraphOpenImmersion.Constructions.etaleBase (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) x ∈ U := by
      change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.targetAmbientMap V W z)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.Etale.coverMap V W z) x) ∈ U
      rw [hxy]
      exact y.property
    exact ⟨⟨x, hxU⟩, Subtype.ext hxy⟩

theorem imageCycleSupport_le_of_graph_bound (S : Set U) (K : Set (Fin d → ℂ))
    (hb : Set.range (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U e) ⊆ S ×ˢ K) :
    Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (Image.Constructions.imageCycleSupport V W z) U (hU.trans (GraphOpen.Constructions.goodAmbient_regular V W z))) ⊆ S := by
  rw [← divisorLocalGraph_firstRange V W z U hU e]
  rintro _ ⟨x, rfl⟩
  exact (hb ⟨x, rfl⟩).1

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphBaseRange.Constructions
