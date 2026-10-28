import OAI.AlgebraicGeometry.Quotients.FiniteDescent.UniversalCech
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AxisModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange

/-! # Detected Frame -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DetectedFrame

noncomputable section

/-! Finite universal axis detectors give a neighborhood trivialization
in a flat projective family, with the cohomology model constructed internally. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.DetectedFrameNeighborhood

variable {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [X.IsSeparated]
variable (π : X ⟶ S) [IsProper π] [Flat π] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π))
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) {ι : Type u} [LinearOrder ι] [Finite ι]
variable (U : ι → X.Opens) (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
variable {T₁ T₂ : ShortComplex (ModuleCat.{u} Γ(S, ⊤))}
variable (r₁ : CechShort.Construction.CechShortCoordinates.target π L.sheaf U ⟶ T₁)
variable (r₂ : CechShort.Construction.CechShortCoordinates.target π L.sheaf U ⟶ T₂)
variable (D₁ : UniversalCech.Construction.UniversalCechDetector.Data Γ(S, ⊤) T₁)
variable (D₂ : UniversalCech.Construction.UniversalCechDetector.Data Γ(S, ⊤) T₂)

include P hU ha D₁ D₂

theorem exists_open (x : S) [IsIntegral (π.fiber x)]
    (he : Nonempty ((L.pullback (π.fiberι x)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber x)))
    (hj : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map r₂)) :
    ∃ V : S.Opens, x ∈ V ∧
      Nonempty ((L.pullback (π ⁻¹ᵁ V).ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ V).toScheme) := by
  obtain ⟨D, φ, hq, _, hfin, hproj, hφ⟩ := AffineCoverModel.Construction.AffineCoverPerfectModel.exists_model π P U hU ha L
  have : QuasiIso φ := hq
  have := hfin 0
  have := hfin 1
  have := hfin 2
  have := hproj 0
  have := hproj 1
  have := hproj 2
  have := D₁.finite
  have := D₁.free
  have := D₂.finite
  have := D₂.free
  have := D₁.baseChange (S.Γevaluation x).hom
  have := D₂.baseChange (S.Γevaluation x).hom
  have : L.sheaf.IsQuasicoherent := LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : QuasiIso (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (π.fiberι x) π (π.fiberToSpecResidueField x)
      (S.fromSpecResidueField x) (π.fiber_fac x) L.sheaf U φ) :=
    CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso (π.fiberι x) π (π.fiberToSpecResidueField x)
      (S.fromSpecResidueField x) L.sheaf U φ (IsPullback.of_hasPullback π (S.fromSpecResidueField x))
      (fun q i => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U ha q i.1) hφ
  exact AxisModel.Construction.AxisModelFrameNeighborhood.exists_open π L U hU φ T₁ T₂ D₁.target D₂.target
    r₁ r₂ D₁.comparison D₂.comparison D₁.first_zero D₂.first_zero hφ x he inferInstance hj

end Construction.DetectedFrameNeighborhood

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DetectedFrame
