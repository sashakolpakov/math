import OAI.RepresentationTheory.Theta.Geometric.Local.ProjectiveCechModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections

/-! # Minimal Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalSections

noncomputable section

/-! Minimal first cycles give actual global sections on every affine
geometric base change of the original family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def scalarFirstCyclesLinearEquiv
    {R T : Type u} [CommRing R] [CommRing T] (g : R →+* T)
    (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    letI : Algebra R T := g.toAlgebra
    ((((ModuleCat.extendScalars g).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker ≃ₗ[T]
      LinearMap.ker (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T (C.sc' 0 1 2)).f.hom := by
  letI : Algebra R T := g.toAlgebra
  exact {
    toFun x := ⟨x.val, x.property⟩
    invFun x := ⟨x.val, x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

def minimalGeometricSectionsEquiv
    {X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T] [IsLocalRing Γ(S, ⊤)]
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
    (M : X.Modules) [M.IsQuasicoherent]
    {I : Type u} [LinearOrder I] [Finite I] (U : I → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ (q : ℕ) (i : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I q), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
    (hφ : ∀ (V : Type u) [AddCommGroup V] [Module Γ(S, ⊤) V],
      QuasiIso (AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map V φ))
    (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    LinearMap.ker (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex Γ(S, ⊤) Γ(T, ⊤) P.complex).f.hom ≃ₗ[Γ(T, ⊤)]
      (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤) := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  have := AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ g M U φ hp ha hφ
  exact (P.baseChangeFirstCyclesEquiv Γ(T, ⊤)).symm.trans
    ((scalarFirstCyclesLinearEquiv g.appTop.hom C).symm.trans
      (AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g hp.w M U hU φ))

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalSections
