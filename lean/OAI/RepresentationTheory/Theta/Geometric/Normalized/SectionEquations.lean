import OAI.RepresentationTheory.Theta.Geometric.ModelAxisNormalization
import OAI.RepresentationTheory.Theta.Geometric.MinimalSectionLocalEquations

/-! # Section Equations -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.SectionEquations

noncomputable section

/-! The normalized sections of the actual geometric family are cut out
by the minimal differential's original coefficients on every affine test. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u
variable {X Y S T : Scheme.{u}} [IsLocalRing Γ(S, ⊤)]
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (π : X ⟶ S) (ρ : Y ⟶ T) (hπ : f ≫ π = ρ ≫ g)
    (hs : s ≫ π = 𝟙 S) (hb : b ≫ ρ = 𝟙 T)
    (M : X.Modules) {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) (i : I)
    (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U) (hU : iSup U = ⊤)
    [hmodel : QuasiIsoAt (AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g hπ M U φ) 0]

include hb hπ hU hmodel in
theorem normalized_geometric_sections_equations
    (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) {J : Type*}
    (basis : Module.Basis J Γ(S, ⊤) P.complex.X₂) (e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁)
    (hu : IsUnit (MinimalNormalizedSections.minimalSectionFunctional P (ModelAxisNormalization.modelAxisFunctional s π hs M U r i hi φ) (e 1))) :
    (∃ a : (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤),
      (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom.app ⊤
        (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj M) a) = (1 : Γ(T, ⊤))) ↔
      Ideal.span (Set.range fun j => basis.repr (P.complex.f (e 1)) j) ≤ RingHom.ker g.appTop.hom := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let v := ModelAxisNormalization.modelAxisFunctional s π hs M U r i hi φ
  let E := AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g hπ M U hU φ
  have hn : (∃ a : (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤),
      (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom.app ⊤
        (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj M) a) = (1 : Γ(T, ⊤))) ↔
      ∃ z : ((((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker,
        KernelBaseChange.scalarFunctionalBaseChange Γ(T, ⊤) v z.val = 1 := by
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨z, rfl⟩ := E.surjective a
      exact ⟨z, (ModelAxisNormalization.modelAxisNormalization_value f b g s h π ρ hπ hs hb M U r i hi φ hU z).symm.trans ha⟩
    · rintro ⟨z, hz⟩
      exact ⟨E z, (ModelAxisNormalization.modelAxisNormalization_value f b g s h π ρ hπ hs hb M U r i hi φ hU z).trans hz⟩
  refine hn.trans (Iff.trans ?_ (MinimalNormalizedSections.normalized_minimal_section_equations P Γ(T, ⊤) basis e v hu))
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.val, z.property, hz⟩
  · rintro ⟨z, hz, hn⟩
    exact ⟨⟨z, hz⟩, hn⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.SectionEquations
