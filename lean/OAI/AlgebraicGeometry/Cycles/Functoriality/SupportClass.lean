import OAI.AlgebraicGeometry.Cycles.Functoriality.Support
import OAI.AlgebraicGeometry.Cycles.Functoriality.UnitProjection
import OAI.AlgebraicGeometry.Cycles.Functoriality.FundamentalDegreeTransport

/-! # Support Class -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.SupportClass.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

/-- The ambient projection formula expressed directly through Poincare
duality in any equal homological degree. -/
theorem poincareCycleClass_projection
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (L : Compacts V.analyticSpace) (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)
    (n : ℕ) (hn : 2 * Z.regularComplexDimension = n)
    (hpn : (p + p) + n = 2 * V.complexDimension) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ) n
      ((V.poincareDuality (p + p) n hpn).hom Z.geometricCycleClass) =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (CycleProjection.Construction.regularAmbientMap Z)
        (A := (CycleProjection.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace))ᶜ)
        (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree Z.regularComplexDimension
        (CycleProjection.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace))
        (CycleProjection.Construction.isCompact_regularAmbientMap_preimage Z L hL) n hn) := by
  cases hn
  exact CycleProjection.Construction.geometricCycleFundamentalClass_projection Z L hL

/-- The geometric class of the whole smooth projective variety is its
actual degree-zero cup unit. -/
theorem fullCycleSupport_geometricCycleClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (Support.Construction.fullCycleSupport V).geometricCycleClass = UnitCap.cohomologyUnit V := by
  let Z := Support.Construction.fullCycleSupport V
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : IsIntegral Z.regularOver.left := inferInstanceAs (IsIntegral Z.regularScheme)
  let : Smooth Z.regularOver.hom := inferInstanceAs (Smooth Z.regularToBase)
  let φ := Z.regularToSupport ≫ Z.toAmbient
  let : IsIso φ := inferInstanceAs (IsIso ((Support.Construction.fullCycleSupport V).regularToSupport ≫
    (Support.Construction.fullCycleSupport V).toAmbient))
  let : IsIso φ.left := (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map_isIso φ
  let : IsOpenImmersion φ.left := inferInstance
  let F := CycleProjection.Construction.regularAmbientMap Z
  have hF : (F : Z.regularAnalyticSpace → V.analyticSpace) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ := by
    funext x
    exact ConcreteCategory.congr_hom (Support.Construction.regularAmbientMap_eq_schemeMap Z) x
  have hlocal : IsLocalDiffeomorph (𝓘(ℂ, Z.regularAnalyticModel))
      (𝓘(ℂ, V.analyticModel)) ω F := by
    rw [hF]
    exact ImageOpen.Construction.isLocalDiffeomorph_nativeScheme_openImmersion φ
  have hbij : Function.Bijective F := ConcreteCategory.bijective_of_isIso F
  have hd : 2 * Z.regularComplexDimension = 2 * V.complexDimension :=
    congrArg (fun k : ℕ => 2 * k) (Support.Construction.fullCycleSupport_regularDimension V)
  let pd := V.poincareDuality (0 + 0) (2 * V.complexDimension) (by omega)
  apply pd.toLinearEquiv.injective
  change pd.hom Z.geometricCycleClass = pd.hom (UnitCap.cohomologyUnit V)
  have hc : ∀ A : IrreducibleCloseds V.carrier,
      (A : Set V.carrier) ⊆ (⊥ : Closeds V.carrier) → 0 < CycleClass.Geometric.DimensionCycles.dimensionCodimension V A := by
    intro A hA
    obtain ⟨x, hx⟩ := A.isIrreducible.nonempty
    exact (hA hx).elim
  apply CompactProjection.Construction.ordinaryHomology_eq_of_compactProjections_outside_closed V ⊥ 0
    (2 * V.complexDimension) (by omega) hc _ _
  intro L _
  have hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen := by
    rw [Support.Construction.fullCycleSupport_regularAmbientOpen_eq_top]
    exact Set.subset_univ _
  have hK := CycleProjection.Construction.isCompact_regularAmbientMap_preimage Z L hL
  have himage : F '' (F ⁻¹' (L : Set V.analyticSpace)) = (L : Set V.analyticSpace) :=
    Set.image_preimage_eq _ hbij.surjective
  have hproj := poincareCycleClass_projection Z L hL (2 * V.complexDimension) hd (by omega)
  have hfund := FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree_injective_toSupport
    Z.regularComplexDimension V.complexDimension F hbij.injective hlocal
    (F ⁻¹' (L : Set V.analyticSpace)) hK (L : Set V.analyticSpace) L.isCompact himage
    (fun _ hx => hx) (2 * V.complexDimension) hd rfl
  exact hproj.trans (hfund.trans (UnitProjection.Construction.poincareUnit_compactProjection V (L : Set V.analyticSpace) L.isCompact).symm)

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.SupportClass.Construction
