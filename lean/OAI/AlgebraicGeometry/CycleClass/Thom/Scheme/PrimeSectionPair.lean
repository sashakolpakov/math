import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionFixedPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothAmbientRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

/-! # Prime Section Pair -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeSectionPair.Constructions.Regular

/-!
# ThomClass: actual section coordinates on the regular cycle support

The local algebraic support identification restricts the native smooth
parameter chart to the actual regular-support inclusion. Both the native
complex compatibility and the exact section coordinate are retained.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Topology ContDiff _root_.Manifold
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionFixedPair.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

/-- A smooth local equation for the actual support supplies a native
normal pair for its actual regular-locus inclusion. -/
theorem exists_regular_section_normalPair_smooth
    (Z : IrreducibleCloseds X.left) (U : X.left.Opens) (hU : IsAffineOpen U)
    (p b c : Γ(X.left, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (hsupp : ∀ y : SectionEvaluation.Constructions.analyticOpen X U,
      SectionEvaluation.Constructions.sectionEvaluationOn X U c y ≠ 0 →
        (SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0 ↔
          y.val ∈ Set.range (RegularSupport.Constructions.supportInclusion X Z)))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X Z))
    (hxU : (RegularSupport.Constructions.regularInclusion X Z) x ∈ SectionEvaluation.Constructions.analyticOpen X U)
    (hxb : SectionEvaluation.Constructions.sectionEvaluationOn X U b ⟨(RegularSupport.Constructions.regularInclusion X Z) x, hxU⟩ ≠ 0)
    (hxc : SectionEvaluation.Constructions.sectionEvaluationOn X U c ⟨(RegularSupport.Constructions.regularInclusion X Z) x, hxU⟩ ≠ 0) :
    ∃ (d : ℕ) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin 1 → ℂ) (RegularSupport.Constructions.regularComplementInclusion X Z) x),
      ∃ hPU : ∀ y ∈ P.neighborhood, y.val ∈ SectionEvaluation.Constructions.analyticOpen X U,
      d + 1 = (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) ∧
      P.ambientChart.MDifferentiable 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) 𝓘(ℂ, (Fin d → ℂ) × (Fin 1 → ℂ)) ∧
      ContMDiffOn 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) 𝓘(ℂ, (Fin d → ℂ) × (Fin 1 → ℂ)) ∞
        P.ambientChart P.ambientChart.source ∧
      ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin 1 → ℂ)) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) ∞
        P.ambientChart.symm P.ambientChart.target ∧
      ∀ y : P.neighborhood, P.normalCoordinate y 0 =
        SectionEvaluation.Constructions.sectionEvaluationOn X U p ⟨y.val.val, hPU y.val y.property⟩ := by
  let xU : SectionEvaluation.Constructions.analyticOpen X U := ⟨(RegularSupport.Constructions.regularInclusion X Z) x, hxU⟩
  have hxp : SectionEvaluation.Constructions.sectionEvaluationOn X U p xU = 0 :=
    (hsupp xU hxc).mpr ((RegularSupport.Constructions.regularInclusion_subset X Z) ⟨x, rfl⟩)
  obtain ⟨d, P, hPU, hd, _, hq, hqi, hcoord⟩ :=
    SectionFixedPair.Constructions.exists_native_section_fixedNormalPair_smooth X U hU p b hp hsm xU hxp hxb
  let W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
    ⟨Subtype.val '' {y : SectionEvaluation.Constructions.analyticOpen X U |
        SectionEvaluation.Constructions.sectionEvaluationOn X U c y ≠ 0},
      (SectionEvaluation.Constructions.analyticOpen X U).isOpenEmbedding'.isOpenMap _
        (isOpen_ne.preimage (SectionEvaluation.Constructions.sectionEvaluationOn X U c).continuous)⟩
  have hxW : (RegularSupport.Constructions.regularInclusion X Z) x ∈ W := ⟨xU, hxc, rfl⟩
  have hxR : (RegularSupport.Constructions.regularInclusion X Z) x ∈ (RegularSupport.Constructions.regularAmbientOpen X Z) :=
    ((RegularSupport.Constructions.regularComplementInclusion X Z) x).property
  obtain ⟨r, hr, hle, hsub⟩ := P.exists_restrictRadius_subset
    (((RegularSupport.Constructions.regularAmbientOpen X Z) ⊓ W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (((RegularSupport.Constructions.regularAmbientOpen X Z) ⊓ W).isOpen.mem_nhds ⟨hxR, hxW⟩)
  let Q := P.restrictRadius r hr hle
  have hQP : Q.neighborhood ⊆ P.neighborhood :=
    P.restrictRadius_neighborhood_subset r hr hle
  have hQR : Q.neighborhood ⊆ (RegularSupport.Constructions.regularAmbientOpen X Z) := fun _ hy => (hsub hy).1
  let R := HodgeConjecture.DegreeTwo.NormalPairAmbientRestriction.Constructions.normalPairRestrictAmbient Q (RegularSupport.Constructions.regularAmbientOpen X Z) hQR
  have hRQ (y : R.neighborhood) : y.val.val ∈ Q.neighborhood :=
    HodgeConjecture.DegreeTwo.NormalPairAmbientRestriction.Constructions.normalPairRestrictAmbient_neighborhood Q (RegularSupport.Constructions.regularAmbientOpen X Z) hQR y
  have hRy (y : R.neighborhood) : y.val.val ∈ SectionEvaluation.Constructions.analyticOpen X U :=
    hPU (hQP (hRQ y))
  have he : (RegularSupport.Constructions.regularComplementInclusion X Z) x =
      HodgeConjecture.DegreeTwo.NormalPairAmbientRestriction.Constructions.supportInOpen (f := fun z : {y : SectionEvaluation.Constructions.analyticOpen X U //
        SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0} => z.val.val)
        (RegularSupport.Constructions.regularAmbientOpen X Z) ⟨⟨xU, hxp⟩, hQR Q.point_mem_neighborhood⟩ := by
    apply Subtype.ext
    rfl
  have hs : ∀ y ∈ R.neighborhood,
      y ∈ Set.range (RegularSupport.Constructions.regularComplementInclusion X Z) ↔
      y ∈ Set.range (HodgeConjecture.DegreeTwo.NormalPairAmbientRestriction.Constructions.supportInOpen (f := fun z : {y : SectionEvaluation.Constructions.analyticOpen X U //
        SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0} => z.val.val)
        (RegularSupport.Constructions.regularAmbientOpen X Z)) := by
    intro y hy
    rw [RegularSupport.Constructions.regularComplementInclusion_range X Z, HodgeConjecture.DegreeTwo.NormalPairAmbientRestriction.Constructions.supportInOpen_range]
    obtain ⟨w, hw, hew⟩ := (hsub (hRQ ⟨y, hy⟩)).2
    have hwc : SectionEvaluation.Constructions.sectionEvaluationOn X U c ⟨y.val, hRy ⟨y, hy⟩⟩ ≠ 0 := by
      have hew' : w = ⟨y.val, hRy ⟨y, hy⟩⟩ := Subtype.ext hew
      exact hew' ▸ hw
    change y.val ∈ Set.range (RegularSupport.Constructions.supportInclusion X Z) ↔ _
    rw [← hsupp ⟨y.val, hRy ⟨y, hy⟩⟩ hwc]
    constructor
    · intro hpz
      exact ⟨⟨⟨y.val, hRy ⟨y, hy⟩⟩, hpz⟩, rfl⟩
    · rintro ⟨z, hez⟩
      have hez' : z.val = ⟨y.val, hRy ⟨y, hy⟩⟩ := Subtype.ext hez
      exact hez' ▸ z.property
  let T := HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions.normalPairReplaceSupport R (RegularSupport.Constructions.regularComplementInclusion X Z) x he hs
  have hTU : ∀ y ∈ T.neighborhood, y.val ∈ SectionEvaluation.Constructions.analyticOpen X U :=
    fun y hy => hRy ⟨y, hy⟩
  have hqs := HodgeConjecture.DegreeTwo.SmoothAmbientRestriction.Constructions.contMDiffOn_subtypeRestr Q.ambientChart hq hqi (RegularSupport.Constructions.regularAmbientOpen X Z)
    ⟨⟨_, hQR Q.point_mem_neighborhood⟩⟩
  refine ⟨d, T, hTU, hd, ?_, hqs.1, hqs.2, ?_⟩
  · exact HodgeConjecture.DegreeTwo.SmoothAmbientRestriction.Constructions.normalPairRestrictAmbient_mdifferentiable Q (RegularSupport.Constructions.regularAmbientOpen X Z) hQR hq hqi
  · intro y
    exact hcoord ⟨y.val.val, hQP (hRQ ⟨y.val, y.property⟩)⟩

end AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeSectionPair.Constructions.Regular

namespace AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeSectionPair.Constructions

/-! Actual divisor section coordinates in the exact native tangent and normal
models of the canonical prime-divisor Thom class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
  SchemeDivisor.Module.Constructions Regular

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (z : {x : X.left // Order.coheight x = 1})

local notation "Z" => OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem exists_prime_section_fixedNormalPair (U : X.left.Opens) (hU : IsAffineOpen U)
    (p b c : Γ(X.left, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (hsupp : ∀ y : SectionEvaluation.Constructions.analyticOpen X U, SectionEvaluation.Constructions.sectionEvaluationOn X U c y ≠ 0 →
      (SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0 ↔ y.val ∈ Set.range (RegularSupport.Constructions.supportInclusion X Z)))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X Z))
    (hxU : RegularSupport.Constructions.regularInclusion X Z x ∈ SectionEvaluation.Constructions.analyticOpen X U)
    (hxb : SectionEvaluation.Constructions.sectionEvaluationOn X U b ⟨RegularSupport.Constructions.regularInclusion X Z x, hxU⟩ ≠ 0)
    (hxc : SectionEvaluation.Constructions.sectionEvaluationOn X U c ⟨RegularSupport.Constructions.regularInclusion X Z x, hxU⟩ ≠ 0) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (RegularSupport.Constructions.regularModel X Z) (Fin 1 → ℂ) (RegularSupport.Constructions.regularComplementInclusion X Z) x,
      ∃ hPU : ∀ y ∈ P.neighborhood, y.val ∈ SectionEvaluation.Constructions.analyticOpen X U,
      P.ambientChart.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, RegularSupport.Constructions.regularModel X Z × (Fin 1 → ℂ)) ∧
      ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, RegularSupport.Constructions.regularModel X Z × (Fin 1 → ℂ))
        ∞ P.ambientChart P.ambientChart.source ∧
      ContMDiffOn 𝓘(ℂ, RegularSupport.Constructions.regularModel X Z × (Fin 1 → ℂ)) 𝓘(ℂ, E)
        ∞ P.ambientChart.symm P.ambientChart.target ∧
      (∀ y : P.neighborhood, P.normalCoordinate y 0 =
        SectionEvaluation.Constructions.sectionEvaluationOn X U p ⟨y.val.val, hPU y.val y.property⟩) ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
        (TopCat.of (RegularSupport.Constructions.regularAmbientOpen X Z)) (Set.range (RegularSupport.Constructions.regularComplementInclusion X Z))ᶜ
        P.openNeighborhood 2 (SchemeDivisor.Module.Constructions.regularDivisorThomClass X z) = P.rationalClassFin := by
  obtain ⟨d, P, hPU, hd, hmd, hq, hqi, hcoord⟩ :=
    Regular.exists_regular_section_normalPair_smooth X Z U hU p b c hp hsm hsupp x hxU hxb hxc
  have hadd := SchemeDivisor.Purity.Constructions.primeRegularDimension_add_one X z
  have hd' : d = Betti.AffineDimension.Realization.functionFieldDifferentialDimension (RegularSupport.Constructions.regularOver X Z).hom := by omega
  subst d
  exact ⟨P, hPU, hmd, hq, hqi, hcoord, SchemeDivisor.Module.Constructions.regularDivisorThomClass_restrict X z x P hmd⟩

end AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeSectionPair.Constructions

end

end OAI
