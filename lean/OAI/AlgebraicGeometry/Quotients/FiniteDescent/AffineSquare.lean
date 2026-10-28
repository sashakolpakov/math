import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGeometric
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.IsTensorProduct
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PushoutModule

/-! # Affine Square -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSquare

noncomputable section

/-! Sections in an affine Cartesian square satisfy the canonical tensor base-change formula. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace Construction.AffineSquareSections

variable {X Y S T : Scheme.{u}} [IsAffine X] [IsAffine S] [IsAffine T]
variable (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : IsPullback f ρ π g) (M : X.Modules) [M.IsQuasicoherent]

def iso :
    (ModuleCat.extendScalars g.appTop.hom).obj
      ((ModuleCat.restrictScalars π.appTop.hom).obj ((AffineSectionIs.Construction.AffineSectionAdjunction.sections X).obj M)) ≅
    (ModuleCat.restrictScalars ρ.appTop.hom).obj
      ((AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).obj ((Scheme.Modules.pullback f).obj M)) := by
  have : IsAffine Y := .of_isPullback h
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := π.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ(Y, ⊤) := ρ.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := (π.appTop ≫ f.appTop).hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hw : π.appTop ≫ f.appTop = g.appTop ≫ ρ.appTop :=
    (isPushout_appTop_of_isPullback h).w
  have : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hw)
  have : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(X, ⊤) Γ(Y, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_appTop_of_isPullback h).flip
  let N := (AffineSectionIs.Construction.AffineSectionAdjunction.sections X).obj M
  let : Module Γ(S, ⊤) N := Module.compHom N π.appTop.hom
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let P := (AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).obj ((Scheme.Modules.pullback f).obj M)
  let : Module Γ(T, ⊤) P := Module.compHom P ρ.appTop.hom
  have : IsScalarTower Γ(T, ⊤) Γ(Y, ⊤) P :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let q : Γ(Y, ⊤) ⊗[Γ(X, ⊤)] N ≃ₗ[Γ(Y, ⊤)] P :=
    (AffineGeometric.Construction.AffineGeometricSections.iso f M).toLinearEquiv
  exact PushoutModule.Construction.PushoutModuleIso.iso Γ(S, ⊤) Γ(X, ⊤) Γ(T, ⊤) Γ(Y, ⊤) N P q

theorem one_tmul (s : (AffineSectionIs.Construction.AffineSectionAdjunction.sections X).obj M) :
    (iso f π ρ g h M).hom ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom]
      (show (ModuleCat.restrictScalars π.appTop.hom).obj ((AffineSectionIs.Construction.AffineSectionAdjunction.sections X).obj M) from s)) =
        PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ⊤ s := by
  have : IsAffine Y := .of_isPullback h
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := π.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ(Y, ⊤) := ρ.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := (π.appTop ≫ f.appTop).hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hw : π.appTop ≫ f.appTop = g.appTop ≫ ρ.appTop :=
    (isPushout_appTop_of_isPullback h).w
  have : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hw)
  have : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(X, ⊤) Γ(Y, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_appTop_of_isPullback h).flip
  let N := (AffineSectionIs.Construction.AffineSectionAdjunction.sections X).obj M
  let : Module Γ(S, ⊤) N := Module.compHom N π.appTop.hom
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let P := (AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).obj ((Scheme.Modules.pullback f).obj M)
  let : Module Γ(T, ⊤) P := Module.compHom P ρ.appTop.hom
  have : IsScalarTower Γ(T, ⊤) Γ(Y, ⊤) P :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let q : Γ(Y, ⊤) ⊗[Γ(X, ⊤)] N ≃ₗ[Γ(Y, ⊤)] P :=
    (AffineGeometric.Construction.AffineGeometricSections.iso f M).toLinearEquiv
  exact (PushoutModule.Construction.PushoutModuleIso.one_tmul Γ(S, ⊤) Γ(X, ⊤) Γ(T, ⊤) Γ(Y, ⊤) N P q s).trans
    (AffineGeometric.Construction.AffineGeometricSections.one_tmul f M s)

end Construction.AffineSquareSections

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSquare
