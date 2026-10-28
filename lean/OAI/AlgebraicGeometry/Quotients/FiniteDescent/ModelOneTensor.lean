import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange

/-! # Model One Tensor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOneTensor

noncomputable section

/-! The model comparison on a pure tensor agrees with canonical Cech pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

universe u

namespace Construction.CechBaseChangeMap

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)

theorem model_one (q : ℕ) (x : D.X q) :
    (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ).f q ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] x) =
      (CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f q (φ.f q x) := by
  change (CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g h M U).f q
    ((ModuleCat.extendScalars g.appTop.hom).map (φ.f q)
      ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] x)) = _
  rw [ModuleCat.ExtendScalars.map_tmul, CechBaseTmul.Construction.CechBaseChangeMap.one_tmul]

def oneCycle (x : (D.d 0 1).hom.ker) :
    ((((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D).d 0 1).hom.ker :=
  ⟨(1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] x.val, by
    change (ModuleCat.extendScalars g.appTop.hom).map (D.d 0 1)
      ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] x.val) = 0
    rw [ModuleCat.ExtendScalars.map_tmul, x.property, TensorProduct.tmul_zero]⟩

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOneTensor
