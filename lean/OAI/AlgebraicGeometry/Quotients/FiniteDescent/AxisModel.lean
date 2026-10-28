import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TwoAxisCycleLift
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ResidueModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberTensor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOrdinaryBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelFrame
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionPair
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorExtensionQuasi

/-! # Axis Model -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AxisModel

noncomputable section

/-! Two axis detectors, compared with a finite projective Cech model,
produce a genuine trivialization near a trivial integral fiber. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.AxisModelFrameNeighborhood

variable {X S : Scheme.{u}} [IsAffine S] (π : X ⟶ S) [IsProper π] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U) [QuasiIsoAt φ 0]
variable [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
variable [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
variable [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
variable (T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} Γ(S, ⊤)))
variable [Module.Finite Γ(S, ⊤) Q₁.X₂] [Module.Free Γ(S, ⊤) Q₁.X₂]
variable [Module.Finite Γ(S, ⊤) Q₂.X₂] [Module.Free Γ(S, ⊤) Q₂.X₂]

include hU

theorem exists_open
    (r₁ : CechShort.Construction.CechShortCoordinates.target π L.sheaf U ⟶ T₁)
    (r₂ : CechShort.Construction.CechShortCoordinates.target π L.sheaf U ⟶ T₂)
    (p₁ : T₁ ⟶ Q₁) (p₂ : T₂ ⟶ Q₂) (h₁ : Q₁.f = 0) (h₂ : Q₂.f = 0)
    (hφ : ∀ (B : Type u) [AddCommGroup B] [Module Γ(S, ⊤) B], QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map B φ))
    (x : S) [IsIntegral (π.fiber x)]
    (he : Nonempty ((L.pullback (π.fiberι x)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber x)))
    (hf : QuasiIsoAt (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (π.fiberι x) π (π.fiberToSpecResidueField x)
      (S.fromSpecResidueField x) (π.fiber_fac x) L.sheaf U φ) 0)
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map p₁)]
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map p₂)]
    (hj : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map r₂)) :
    ∃ V : S.Opens, x ∈ V ∧
      Nonempty ((L.pullback (π ⁻¹ᵁ V).ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ V).toScheme) := by
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₁ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 0))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₁ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 0))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₂ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 1))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₂ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 1))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₃ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 2))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₃ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 2))
  have := hf
  let F := Over.mk (π.fiberToSpecResidueField x)
  have : IsProper F.hom := inferInstanceAs (IsProper (pullback.snd π (S.fromSpecResidueField x)))
  have : IsIntegral F.left := inferInstanceAs (IsIntegral (π.fiber x))
  have hn := SectionPair.Construction.SectionPairTriviality.nontrivial_sections_of_trivial F (L.pullback (π.fiberι x)) he.some
  have hs₀ := (ModelSection.Construction.ModelSectionSupport.sections_iff (π.fiberι x) π (π.fiberToSpecResidueField x)
    (S.fromSpecResidueField x) (π.fiber_fac x) L.sheaf U hU φ
      (default : Spec (S.residueField x))).mp hn
  have hs : S.toSpecΓ x ∈ Module.support Γ(S, ⊤) (KernelSupportIs.Construction.KernelSupport.dualCokernel (D.d 0 1).hom) := by
    have hpoint := S.fromSpecResidueField_apply x (default : Spec (S.residueField x))
    exact hpoint ▸ hs₀
  let A := S.presheaf.stalk x
  let : Algebra Γ(S, ⊤) A := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : Module.Flat Γ(S, ⊤) A := FiberScalar.Construction.FiberScalarMaps.stalk_flat S x
  obtain ⟨z, hz, hne⟩ := ResidueModel.Construction.ResidueModelCycles.exists_cycle S x (D.sc' 0 1 2) hs
  let ψ := OrderedCechShort.Construction.OrderedCechShortComparison.comparison π L.sheaf U φ
  have : QuasiIso (((ModuleCat.extendScalars (S.Γevaluation x).hom).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) := TensorExtensionQuasi.Construction.TensorExtension.quasiIso (S.Γevaluation x).hom φ hφ
  have : ShortComplex.QuasiIso ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map ψ) :=
    ModelOrdinaryBaseChange.Construction.OrderedCechShortComparison.baseChange_quasiIso π L.sheaf U φ (S.Γevaluation x).hom
  let a := (algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap Γ(S, ⊤) A)
  have : ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map ψ) :=
    show ShortComplex.QuasiIso ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map ψ)
      from inferInstance
  have : ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map p₁) :=
    show ShortComplex.QuasiIso ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map p₁)
      from inferInstance
  have : ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map p₂) :=
    show ShortComplex.QuasiIso ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map p₂)
      from inferInstance
  obtain ⟨m, hm, hmn⟩ := TwoAxisCycleLift.Construction.FlatTwoAxisCycleLift.exists_cycle (A := A) (D.sc' 0 1 2)
    (CechShort.Construction.CechShortCoordinates.target π L.sheaf U) T₁ T₂ Q₁ Q₂ ψ r₁ r₂ p₁ p₂ h₁ h₂ hj z hz hne
  exact ModelFrame.Construction.ModelFrameNeighborhood.exists_open π L U hU φ x he hf ⟨m, hm⟩
    (FiberTensor.Construction.FiberTensorSurvival.nonzero S x (D.X 0) m hmn)

end Construction.AxisModelFrameNeighborhood

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AxisModel
