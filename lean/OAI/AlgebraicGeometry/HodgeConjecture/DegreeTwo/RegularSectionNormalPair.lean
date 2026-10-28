import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicSectionNormalPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothAmbientRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrimeDivisorCycleSupport
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

/-! # Regular Section Normal Pair -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularSectionNormalPair.Constructions

noncomputable section

/-!
# DegreeTwo: actual section coordinates on the regular cycle support

The local algebraic support identification restricts the native smooth
parameter chart to the actual regular-support inclusion. Both the native
complex compatibility and the exact section coordinate are retained.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Topology ContDiff _root_.Manifold
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance regularSectionNormalPairIntegral : IsIntegral V.toOver.left := V.property
local instance regularSectionNormalPairSmooth : Smooth V.toOver.hom := V.presentation.smooth

/-- A smooth local equation for the actual support supplies a native
normal pair for its actual regular-locus inclusion. -/
theorem exists_regular_section_normalPair
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (U : V.carrier.Opens) (hU : IsAffineOpen U)
    (p b c : Γ(V.carrier, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra V.structureMap U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (hsupp : ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U,
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c y ≠ 0 →
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y = 0 ↔
          y.val ∈ Set.range Z.analyticInclusion))
    (x : Z.regularAnalyticSpace)
    (hxU : Z.regularAnalyticToAmbient x ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U)
    (hxb : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b ⟨Z.regularAnalyticToAmbient x, hxU⟩ ≠ 0)
    (hxc : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c ⟨Z.regularAnalyticToAmbient x, hxU⟩ ≠ 0) :
    ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ Z.regularComplementInclusion x),
      ∃ hPU : ∀ y ∈ P.neighborhood, y.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U,
      d + 1 = V.complexDimension ∧
      P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, (Fin d → ℂ) × ℂ) ∧
      ∀ y : P.neighborhood, P.normalCoordinate y =
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p ⟨y.val.val, hPU y.val y.property⟩ := by
  let xU : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U := ⟨Z.regularAnalyticToAmbient x, hxU⟩
  have hxp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p xU = 0 :=
    (hsupp xU hxc).mpr (Z.range_regularAnalyticToAmbient_subset ⟨x, rfl⟩)
  obtain ⟨d, P, hPU, hd, _, hq, hqi, hcoord⟩ :=
    IntrinsicSectionNormalPair.Constructions.exists_native_section_normalPair_smooth V.presentation U hU p b hp hsm xU hxp hxb
  let W : Opens V.analyticSpace :=
    ⟨Subtype.val '' {y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U |
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c y ≠ 0},
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U).isOpenEmbedding'.isOpenMap _
        (isOpen_ne.preimage (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c).continuous)⟩
  have hxW : Z.regularAnalyticToAmbient x ∈ W := ⟨xU, hxc, rfl⟩
  have hxR : Z.regularAnalyticToAmbient x ∈ Z.regularAmbientOpen :=
    (Z.regularComplementInclusion x).property
  obtain ⟨r, hr, hle, hsub⟩ := P.exists_restrictRadius_subset
    ((Z.regularAmbientOpen ⊓ W : Opens V.analyticSpace) : Set V.analyticSpace)
    ((Z.regularAmbientOpen ⊓ W).isOpen.mem_nhds ⟨hxR, hxW⟩)
  let Q := P.restrictRadius r hr hle
  have hQP : Q.neighborhood ⊆ P.neighborhood :=
    P.restrictRadius_neighborhood_subset r hr hle
  have hQR : Q.neighborhood ⊆ Z.regularAmbientOpen := fun _ hy => (hsub hy).1
  let R := NormalPairAmbientRestriction.Constructions.normalPairRestrictAmbient Q Z.regularAmbientOpen hQR
  have hRQ (y : R.neighborhood) : y.val.val ∈ Q.neighborhood :=
    NormalPairAmbientRestriction.Constructions.normalPairRestrictAmbient_neighborhood Q Z.regularAmbientOpen hQR y
  have hRy (y : R.neighborhood) : y.val.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U :=
    hPU (hQP (hRQ y))
  have he : Z.regularComplementInclusion x =
      NormalPairAmbientRestriction.Constructions.supportInOpen (f := fun z : {y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U //
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y = 0} => z.val.val)
        Z.regularAmbientOpen ⟨⟨xU, hxp⟩, hQR Q.point_mem_neighborhood⟩ := by
    apply Subtype.ext
    rfl
  have hs : ∀ y ∈ R.neighborhood,
      y ∈ Set.range Z.regularComplementInclusion ↔
      y ∈ Set.range (NormalPairAmbientRestriction.Constructions.supportInOpen (f := fun z : {y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U //
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y = 0} => z.val.val)
        Z.regularAmbientOpen) := by
    intro y hy
    rw [Z.range_regularComplementInclusion, NormalPairAmbientRestriction.Constructions.supportInOpen_range]
    obtain ⟨w, hw, hew⟩ := (hsub (hRQ ⟨y, hy⟩)).2
    have hwc : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c ⟨y.val, hRy ⟨y, hy⟩⟩ ≠ 0 := by
      have hew' : w = ⟨y.val, hRy ⟨y, hy⟩⟩ := Subtype.ext hew
      exact hew' ▸ hw
    change y.val ∈ Set.range Z.analyticInclusion ↔ _
    rw [← hsupp ⟨y.val, hRy ⟨y, hy⟩⟩ hwc]
    constructor
    · intro hpz
      exact ⟨⟨⟨y.val, hRy ⟨y, hy⟩⟩, hpz⟩, rfl⟩
    · rintro ⟨z, hez⟩
      have hez' : z.val = ⟨y.val, hRy ⟨y, hy⟩⟩ := Subtype.ext hez
      exact hez' ▸ z.property
  let T := NormalPairReindex.Constructions.normalPairReplaceSupport R Z.regularComplementInclusion x he hs
  have hTU : ∀ y ∈ T.neighborhood, y.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U :=
    fun y hy => hRy ⟨y, hy⟩
  refine ⟨d, T, hTU, hd, ?_, ?_⟩
  · exact SmoothAmbientRestriction.Constructions.normalPairRestrictAmbient_mdifferentiable Q Z.regularAmbientOpen hQR hq hqi
  · intro y
    exact hcoord ⟨y.val.val, hQP (hRQ ⟨y.val, y.property⟩)⟩

theorem exists_prime_regular_section_normalPair
    (U : V.carrier.Opens) (hU : IsAffineOpen U)
    (z : {z : V.carrier // Order.coheight z = 1}) (hzU : z.val ∈ U)
    (p b : Γ(V.carrier, U))
    (hp : Irreducible (V.carrier.presheaf.germ U z.val hzU p))
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra V.structureMap U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b))) :
    ∃ c : Γ(V.carrier, U), IsUnit (V.carrier.presheaf.germ U z.val hzU c) ∧
      ∀ (x : (PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z).regularAnalyticSpace)
        (hxU : (PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z).regularAnalyticToAmbient x ∈
          DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U),
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b
          ⟨(PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z).regularAnalyticToAmbient x, hxU⟩ ≠ 0 →
        DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c
          ⟨(PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z).regularAnalyticToAmbient x, hxU⟩ ≠ 0 →
        ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
          (PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z).regularComplementInclusion x),
          ∃ hPU : ∀ y ∈ P.neighborhood, y.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U,
          d + 1 = V.complexDimension ∧
          P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
            𝓘(ℂ, (Fin d → ℂ) × ℂ) ∧
          ∀ y : P.neighborhood, P.normalCoordinate y =
            DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p ⟨y.val.val, hPU y.val y.property⟩ := by
  obtain ⟨c, hc, hsupp⟩ :=
    PrimeDivisorCycleSupport.Constructions.section_uniformizer_primeCycleSupport_neighborhood V U hU z hzU p hp
  have hp0 : p ≠ 0 := by
    intro he
    apply hp.ne_zero
    rw [he, map_zero]
  exact ⟨c, hc, fun x hxU hxb hxc =>
    exists_regular_section_normalPair V (PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z) U hU p b c hp0
      hsm hsupp x hxU hxb hxc⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularSectionNormalPair.Constructions
