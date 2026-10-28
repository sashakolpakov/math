import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomPrincipalExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluingNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardCoherence

/-! # Internal Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.InternalHom

noncomputable section

/-! A closed immersion preserves the actual internal Hom out of a
quasicoherent module. The comparison is normalized by literal evaluation
on every affine ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
  (M N : X.Modules) [M.IsQuasicoherent]

abbrev image (L : X.Modules) := (Scheme.Modules.pushforward i).obj L
abbrev source := image i (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N)
abbrev target := ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (image i M) (image i N)

local instance : (image i M).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i

variable (U : Y.Opens)

local instance algebra : Algebra Γ(Y, U) Γ(X, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
local instance scalar (L : X.Modules) : Module Γ(Y, U) Γ(L, i ⁻¹ᵁ U) :=
  Module.compHom Γ(L, i ⁻¹ᵁ U) (i.app U).hom
local instance tower (L : X.Modules) : IsScalarTower Γ(Y, U) Γ(X, i ⁻¹ᵁ U) Γ(L, i ⁻¹ᵁ U) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def sectionEquiv (hU : IsAffineOpen U) : Γ(source i M N, U) ≃ₗ[Γ(Y, U)] Γ(target i M N, U) :=
  ((Affine.HomSectionsEquiv.equiv (i ⁻¹ᵁ U) (hU.preimage i) M N).restrictScalars Γ(Y, U)).trans
    ((SurjectiveScalarHom.equiv Γ(Y, U) Γ(X, i ⁻¹ᵁ U) (i.app_surjective U hU)
      Γ(M, i ⁻¹ᵁ U) Γ(N, i ⁻¹ᵁ U)).trans
      (Affine.HomSectionsEquiv.equiv U hU (image i M) (image i N)).symm)

theorem evaluation (hU : IsAffineOpen U) (z : Γ(source i M N, U)) (m : Γ(image i M, U)) :
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen (image i M) (image i N) U (sectionEquiv i M N U hU z) m =
      ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N (i ⁻¹ᵁ U) z m := by
  change Affine.HomSectionsEquiv.equiv U hU (image i M) (image i N)
    ((Affine.HomSectionsEquiv.equiv U hU (image i M) (image i N)).symm _) m = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem principal (hU : IsAffineOpen U) (r : Γ(Y, U)) (z : Γ(source i M N, U)) :
    sectionEquiv i M N (Y.basicOpen r) (hU.basicOpen r)
      ((source i M N).presheaf.map (homOfLE (Y.basicOpen_le r)).op z) =
    (target i M N).presheaf.map (homOfLE (Y.basicOpen_le r)).op (sectionEquiv i M N U hU z) := by
  apply Affine.HomPrincipalExt.ext U hU r (image i M) (image i N)
  intro m
  rw [evaluation, Affine.HomEvaluation.restriction, evaluation]
  exact Affine.HomEvaluation.restriction M N (i ⁻¹ᵁ U)
    ((TopologicalSpace.Opens.map i.base).map (homOfLE (Y.basicOpen_le r))) z m

omit [IsClosedImmersion i] [M.IsQuasicoherent] in
theorem affine_neighborhood (U : Y.Opens) (x : Y) (hx : x ∈ U) :
    ∃ V, IsAffineOpen V ∧ True ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hx
  exact ⟨V, hV, trivial, hxV, hVU⟩

def iso : source i M N ≅ target i M N :=
  Principal.BasisGluing.iso (source i M N) (target i M N) (fun _ => True)
    (fun U hU _ => (sectionEquiv i M N U hU).toLinearMap)
    (fun _ _ _ _ => trivial) (fun U hU _ r z => principal i M N U hU r z)
    affine_neighborhood (fun U hU _ => (sectionEquiv i M N U hU).bijective)

theorem iso_app (hU : IsAffineOpen U) (z : Γ(source i M N, U)) :
    (iso i M N).hom.app U z = sectionEquiv i M N U hU z :=
  Principal.BasisGluingNormalization.iso_app (source i M N) (target i M N) (fun _ => True)
    (fun U hU _ => (sectionEquiv i M N U hU).toLinearMap)
    (fun _ _ _ _ => trivial) (fun U hU _ r z => principal i M N U hU r z)
    affine_neighborhood (fun U hU _ => (sectionEquiv i M N U hU).bijective) U hU trivial z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.InternalHom
