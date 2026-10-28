import OAI.AlgebraicGeometry.Cycles.Functoriality.CompactDiagram
import OAI.AlgebraicGeometry.Cycles.Functoriality.BoundaryContainment
import OAI.AlgebraicGeometry.Cycles.Functoriality.IntrinsicCompactDegree

/-! # Compact Compatibility -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.CompactCompatibility.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

/-- A commuting finite covering of smooth support opens gives the
cycle-class pushforward equality at every retained compact ambient set. -/
theorem poincareCycleClass_compact_covering_compatibility
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q)
    (f : X.toOver ⟶ Y.toOver)
    (d e : ℕ) {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    [T2Space P] [T2Space Q] [SecondCountableTopology P] [SecondCountableTopology Q]
    [ChartedSpace (Fin d → ℂ) P] [ChartedSpace (Fin e → ℂ) Q]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 P] [IsManifold (𝓘(ℂ, Fin e → ℂ)) 1 Q]
    (jZ : TopCat.of P ⟶ TopCat.of Z.regularAnalyticSpace)
    (jT : TopCat.of Q ⟶ TopCat.of T.regularAnalyticSpace)
    (hjZ : Topology.IsOpenEmbedding jZ) (hjT : Topology.IsOpenEmbedding jT)
    (hlZ : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Z.regularAnalyticModel)) ω jZ)
    (hlT : IsLocalDiffeomorph (𝓘(ℂ, Fin e → ℂ)) (𝓘(ℂ, T.regularAnalyticModel)) ω jT)
    (h : TopCat.of P ⟶ TopCat.of Q) (hh : IsProperMap h)
    (hlh : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin e → ℂ)) ω h)
    (hsquare : (jZ ≫ CycleProjection.Construction.regularAmbientMap Z) ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f =
      h ≫ (jT ≫ CycleProjection.Construction.regularAmbientMap T))
    (degree : ℕ) (hdegree : ∀ y : Q, Nat.card (h ⁻¹' {y}) = degree)
    (n : ℕ) (hd : 2 * d = n) (he : 2 * e = n)
    (hZ : 2 * Z.regularComplexDimension = n) (hT : 2 * T.regularComplexDimension = n)
    (hp : (p + p) + n = 2 * X.complexDimension) (hq : (q + q) + n = 2 * Y.complexDimension)
    (L : Compacts Y.analyticSpace)
    (hLZ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set Y.analyticSpace) ⊆ Z.regularAmbientOpen)
    (hLT : (L : Set Y.analyticSpace) ⊆ T.regularAmbientOpen)
    (hRangeZ : CycleProjection.Construction.regularAmbientMap Z ⁻¹' (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set Y.analyticSpace)) ⊆
      Set.range jZ)
    (hRangeT : CycleProjection.Construction.regularAmbientMap T ⁻¹' (L : Set Y.analyticSpace) ⊆ Set.range jT) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of Y.analyticSpace) (L : Set Y.analyticSpace)ᶜ) n
      (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n
        ((X.poincareDuality (p + p) n hp).hom Z.geometricCycleClass)) =
    (degree : ℚ) • HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of Y.analyticSpace) (L : Set Y.analyticSpace)ᶜ) n
      ((Y.poincareDuality (q + q) n hq).hom T.geometricCycleClass) := by
  let F : TopCat.of X.analyticSpace ⟶ TopCat.of Y.analyticSpace := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f
  let K : Compacts X.analyticSpace :=
    ⟨F ⁻¹' (L : Set Y.analyticSpace), (L.isCompact.isClosed.preimage F.hom.continuous).isCompact⟩
  let u := jZ ≫ CycleProjection.Construction.regularAmbientMap Z
  let v := jT ≫ CycleProjection.Construction.regularAmbientMap T
  let a := (X.poincareDuality (p + p) n hp).hom Z.geometricCycleClass
  have hsource : IsCompact (u ⁻¹' (K : Set X.analyticSpace)) :=
    CycleOpenProjection.Construction.isCompact_openRegularPreimage Z jZ hjZ K hLZ hRangeZ
  have htarget : IsCompact (v ⁻¹' (L : Set Y.analyticSpace)) :=
    CycleOpenProjection.Construction.isCompact_openRegularPreimage T jT hjT L hLT hRangeT
  have hprojZ := CycleOpenProjection.Construction.poincareCycleClass_projection_from_open Z d jZ hjZ hlZ K hLZ hRangeZ n hd hZ hp
  have hprojT := CycleOpenProjection.Construction.poincareCycleClass_projection_from_open T e jT hjT hlT L hLT hRangeT n he hT hq
  let rF := HomologicalComplex.homologyMap
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ F (A := (K : Set X.analyticSpace)ᶜ)
      (B := (L : Set Y.analyticSpace)ᶜ) (fun _ hx => hx)) n
  have hnat := ConcreteCategory.congr_hom
    (CompactProjection.Construction.homologyPushforward_compactProjection F (L : Set Y.analyticSpace) n) a
  have hcomp := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ u F
      (A := (u ⁻¹' (K : Set X.analyticSpace))ᶜ) (B := (K : Set X.analyticSpace)ᶜ)
      (C := (L : Set Y.analyticSpace)ᶜ) (fun _ hx => hx) (fun _ hx => hx) n)
    (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree d (u ⁻¹' (K : Set X.analyticSpace)) hsource n hd)
  have hcongr := CompactDiagram.Construction.rationalCompactFundamentalClassInDegree_push_congr d (u ≫ F) (h ≫ v)
    hsquare (L : Set Y.analyticSpace) hsource (hh.isCompact_preimage htarget) n hd
  have hcover := CompactDiagram.Construction.rationalCompactFundamentalClassInDegree_comp_degree d e h hh hlh degree hdegree
    v (L : Set Y.analyticSpace) htarget n hd he
  exact hnat.trans ((congrArg rF hprojZ).trans (hcomp.trans (hcongr.trans
    (hcover.trans (congrArg (fun z => (degree : ℚ) • z) hprojT.symm)))))

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.CompactCompatibility.Construction
