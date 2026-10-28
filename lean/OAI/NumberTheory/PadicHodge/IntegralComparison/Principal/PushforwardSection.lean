import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne

/-! # Pushforward Section -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSection

noncomputable section

/-! A section of a module on the inverse image of an affine open
defines multiplication on the entire actual principal-open diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (ω : Γ(N, f ⁻¹ᵁ U))

abbrev source := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
abbrev target := (Scheme.Modules.pushforward f).obj N

abbrev sourceInclusion (r : SectionPresheaf.Index U) : f ⁻¹ᵁ SectionPresheaf.openSubset U r ⟶ f ⁻¹ᵁ U :=
  homOfLE (f.preimage_mono (Y.basicOpen_le r.val))

abbrev sourceArrow {r s : SectionPresheaf.Index U} (a : r ⟶ s) :
    f ⁻¹ᵁ SectionPresheaf.openSubset U r ⟶ f ⁻¹ᵁ SectionPresheaf.openSubset U s :=
  homOfLE (f.preimage_mono (SectionPresheaf.arrow U hU a).le)

local instance nativeModule (r : SectionPresheaf.Index U) :
    Module Γ(X, f ⁻¹ᵁ SectionPresheaf.openSubset U r) ((SectionPresheaf.modules U hU (target f N)).obj (op r)) :=
  inferInstanceAs (Module Γ(X, f ⁻¹ᵁ SectionPresheaf.openSubset U r) Γ(N, f ⁻¹ᵁ SectionPresheaf.openSubset U r))

def component (r : SectionPresheaf.Index U) :
    (SectionPresheaf.modules U hU (source f)).obj (op r) →ₗ[Γ(Y, U)]
      (SectionPresheaf.modules U hU (target f N)).obj (op r) where
  toFun x := (show Γ(X, f ⁻¹ᵁ SectionPresheaf.openSubset U r) from x) •
    N.presheaf.map (sourceInclusion f U r).op ω
  map_add' x y := by
    change Γ(X, f ⁻¹ᵁ SectionPresheaf.openSubset U r) at x y
    exact add_smul x y _
  map_smul' a x := by
    change Γ(X, f ⁻¹ᵁ SectionPresheaf.openSubset U r) at x
    change (f.app (SectionPresheaf.openSubset U r) (algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U r) a) * x) •
        N.presheaf.map (sourceInclusion f U r).op ω =
      f.app (SectionPresheaf.openSubset U r) (algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U r) a) •
        (x • N.presheaf.map (sourceInclusion f U r).op ω)
    exact mul_smul _ _ _

def map : SectionPresheaf.modules U hU (source f) ⟶ SectionPresheaf.modules U hU (target f N) where
  app r := ModuleCat.ofHom (component f U hU N ω r.unop)
  naturality r s a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Γ(X, f ⁻¹ᵁ SectionPresheaf.openSubset U r.unop) at x
    change (X.presheaf.map (sourceArrow f U hU a.unop).op x) •
      N.presheaf.map (sourceInclusion f U s.unop).op ω =
      N.presheaf.map (sourceArrow f U hU a.unop).op
        (x • N.presheaf.map (sourceInclusion f U r.unop).op ω)
    rw [N.map_smul]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
    rfl

theorem atOne (x : Γ(X, f ⁻¹ᵁ U)) :
    (PushforwardSection.map f U hU N ω).app (op (AtOne.object U))
      (AtOne.equiv U (source f) x) =
    AtOne.equiv U (target f N) (x • ω) := by
  change (X.presheaf.map (sourceInclusion f U (AtOne.object U)).op x) •
      N.presheaf.map (sourceInclusion f U (AtOne.object U)).op ω =
    N.presheaf.map (sourceInclusion f U (AtOne.object U)).op (x • ω)
  exact (N.map_smul (sourceInclusion f U (AtOne.object U)) x ω).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSection
