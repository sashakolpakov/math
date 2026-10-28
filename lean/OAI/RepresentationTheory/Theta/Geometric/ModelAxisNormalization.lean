import OAI.RepresentationTheory.Theta.Geometric.CechAxisTensorComparison
import OAI.RepresentationTheory.Theta.Geometric.CechAxisSectionValue
import OAI.RepresentationTheory.Theta.Geometric.MinimalNormalizedSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections

/-! # Model Axis Normalization -/

namespace OAI.RepresentationTheory.Theta.Geometric.ModelAxisNormalization

noncomputable section

/-! The original cochain model's axis functional measures the actual
normalization of its global sections after every affine base change. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u
variable {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (π : X ⟶ S) (ρ : Y ⟶ T) (hπ : f ≫ π = ρ ≫ g)
    (hs : s ≫ π = 𝟙 S) (hb : b ≫ ρ = 𝟙 T)
    (M : X.Modules) {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) (i : I)
    (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)

def modelAxisFunctional : C.X 0 →ₗ[Γ(S, ⊤)] Γ(S, ⊤) :=
  (CechAxisFunctional.cechAxisFunctional π s hs M r U i hi).comp (φ.f 0).hom

variable (hU : iSup U = ⊤)
    [QuasiIsoAt (AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g hπ M U φ) 0]

include hb in
theorem modelAxisNormalization_value :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ z : ((((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker,
      (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom.app ⊤
        (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj M)
          (AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g hπ M U hU φ z)) =
      Normalized.KernelBaseChange.scalarFunctionalBaseChange Γ(T, ⊤) (modelAxisFunctional s π hs M U r i hi φ) z.val := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro z
  let r' := AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r
  let i' := CechAxisBaseChange.cechAxisOpen_baseChange f b g s h U i hi
  let U' := fun j => f ⁻¹ᵁ U j
  let a := AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i
  let W := AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U' 0 a
  let u := AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g hπ M U hU φ z
  have hc := AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections_coordinate f π ρ g hπ M U hU φ z a
  have he := CechAxisSectionValue.axisSectionFunctional_restriction ρ b hb ((Scheme.Modules.pullback f).obj M) r' W i' u
  refine he.symm.trans ((congrArg (CechAxisFunctional.axisSectionFunctional ρ b hb
    ((Scheme.Modules.pullback f).obj M) r' W i') hc).trans ?_)
  have ht := CechAxisTensorComparison.cechAxisFunctional_tensorBaseChange f b g s h π ρ hπ hs hb M r U i hi
    ((φ.f 0).hom.baseChange Γ(T, ⊤) z.val)
  exact ht.trans (MinimalNormalizedSections.scalarFunctionalBaseChange_comp Γ(T, ⊤)
    (CechAxisFunctional.cechAxisFunctional π s hs M r U i hi) (φ.f 0).hom z.val).symm

end

end OAI.RepresentationTheory.Theta.Geometric.ModelAxisNormalization
