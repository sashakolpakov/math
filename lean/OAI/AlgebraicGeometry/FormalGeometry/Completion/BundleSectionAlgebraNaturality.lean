import OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleSectionAlgebra
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ModelSectionComposition
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarKernelAlgebraNaturality

/-! # Bundle Section Algebra Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.BundleSectionAlgebraNaturality

noncomputable section

/-! The finite-type algebra classifying a projective line-bundle family's
global sections is compatible with actual geometric base change. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

theorem finiteModelSectionAlgebraEquiv_natural
    {X Y Z S T T' : Scheme.{u}} [IsAffine S] [IsAffine T] [IsAffine T']
    (f : Y ⟶ X) (j : Z ⟶ Y) (π : X ⟶ S) (ρ : Y ⟶ T) (τ : Z ⟶ T')
    (g : T ⟶ S) (t : T' ⟶ T) (hp : IsPullback f ρ π g) (hj : j ≫ ρ = τ ≫ t)
    (ho : IsPullback (j ≫ f) τ π (t ≫ g))
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
    [Module.Finite Γ(S, ⊤) (C.X 0)] [Module.Projective Γ(S, ⊤) (C.X 0)]
    [Module.Finite Γ(S, ⊤) (C.X 1)] [Module.Projective Γ(S, ⊤) (C.X 1)]
    (hφ : ∀ (A : Type u) [AddCommGroup A] [Module Γ(S, ⊤) A],
      QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ))
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤)) :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    letI : Algebra Γ(S, ⊤) Γ(T', ⊤) := (t ≫ g).appTop.hom.toAlgebra
    LineBundleSectionAlgebra.Construction.finiteModelSectionAlgebraEquiv (j ≫ f) π τ (t ≫ g) ho M U hU ha φ hφ
      (GlobalSectionComposition.Construction.globalSectionCompositePullback f j M s) =
    (ScalarKernelAlgebraNaturality.Construction.scalarTransitionAlgHomOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom
      (ModelCoordinateComposition.Construction.appTop_comp_ringHom g t)).comp (LineBundleSectionAlgebra.Construction.finiteModelSectionAlgebraEquiv f π ρ g hp M U hU ha φ hφ s) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(T', ⊤) := (t ≫ g).appTop.hom.toAlgebra
  have := Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ g M U φ hp ha hφ
  have := Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso (j ≫ f) π τ (t ≫ g) M U φ ho ha hφ
  let e := Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g hp.w M U hU φ
  let e' := Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections (j ≫ f) π τ (t ≫ g) ho.w M U hU φ
  have hn := ModelSectionComposition.Construction.modelSection_composite_pullback f j π ρ τ g t hp.w hj M U hU φ (e.symm s)
  change GlobalSectionComposition.Construction.globalSectionCompositePullback f j M (e (e.symm s)) =
    e' (ScalarKernelTransition.Construction.scalarCochainKernelTransitionOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom
      (ModelCoordinateComposition.Construction.appTop_comp_ringHom g t) C (e.symm s)) at hn
  rw [e.apply_symm_apply] at hn
  change ScalarKernelAlgebraNaturality.Construction.scalarKernelAlgebraEquiv (t ≫ g).appTop.hom C
    (e'.symm (GlobalSectionComposition.Construction.globalSectionCompositePullback f j M s)) =
    (ScalarKernelAlgebraNaturality.Construction.scalarTransitionAlgHomOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom
      (ModelCoordinateComposition.Construction.appTop_comp_ringHom g t)).comp (ScalarKernelAlgebraNaturality.Construction.scalarKernelAlgebraEquiv g.appTop.hom C (e.symm s))
  have hk := (congrArg e'.symm hn).trans (e'.symm_apply_apply _)
  exact (congrArg (ScalarKernelAlgebraNaturality.Construction.scalarKernelAlgebraEquiv (t ≫ g).appTop.hom C) hk).trans
    (ScalarKernelAlgebraNaturality.Construction.scalarKernelAlgebraEquiv_natural g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom
      (ModelCoordinateComposition.Construction.appTop_comp_ringHom g t) C (e.symm s))

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.BundleSectionAlgebraNaturality
