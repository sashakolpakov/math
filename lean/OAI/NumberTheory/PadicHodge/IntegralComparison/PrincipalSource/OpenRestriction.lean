import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSectionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence

/-! # Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction

noncomputable section

/-! Restriction to an actual source open on the original ambient
principal diagram. The coefficient map is the open-immersion restriction
unit, pushed through the original two scheme morphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (N : Y.Modules)

abbrev extension := (Scheme.Modules.pushforward V.ι).obj (N.restrict V.ι)
abbrev image := (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pushforward f).obj N)

def coefficientMap : image f i N ⟶ image f i (extension V N) :=
  (Scheme.Modules.pushforward i).map
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictAdjunction V.ι).unit.app N))

def map : Principal.SectionPresheaf.modules U hU (image f i N) ⟶ Principal.SectionPresheaf.modules U hU (image f i (extension V N)) :=
  Principal.SectionPresheaf.moduleHom U hU (coefficientMap f i V N)

abbrev openPart (r : Principal.SectionPresheaf.Index U) := V.ι ''ᵁ
  (V.ι ⁻¹ᵁ (f ⁻¹ᵁ (i ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r)))

theorem openPart_eq (r : Principal.SectionPresheaf.Index U) : openPart f i U V r = V ⊓ f ⁻¹ᵁ (i ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r) := by
  rw [openPart, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

theorem map_app (r : Principal.SectionPresheaf.Index U) (x : Γ(N, f ⁻¹ᵁ (i ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r))) :
    (OpenRestriction.map f i U hU V N).app (op r) x =
      N.presheaf.map (homOfLE (V.ι.image_preimage_le (f ⁻¹ᵁ (i ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r)))).op x :=
  rfl

def restrictedSection (ω : Γ((Scheme.Modules.pushforward f).obj N, i ⁻¹ᵁ U)) :
    Γ((Scheme.Modules.pushforward f).obj (extension V N), i ⁻¹ᵁ U) :=
  ((Scheme.Modules.pushforward f).map
    ((Scheme.Modules.restrictAdjunction V.ι).unit.app N)).app (i ⁻¹ᵁ U) ω

theorem section_apply (ω : Γ((Scheme.Modules.pushforward f).obj N, i ⁻¹ᵁ U)) :
    restrictedSection f i U V N ω =
      N.presheaf.map (homOfLE (V.ι.image_preimage_le (f ⁻¹ᵁ (i ⁻¹ᵁ U)))).op ω := rfl

theorem symbol (ω : Γ((Scheme.Modules.pushforward f).obj N, i ⁻¹ᵁ U)) :
    Principal.PushforwardSection.map i U hU ((Scheme.Modules.pushforward f).obj N) ω ≫
        OpenRestriction.map f i U hU V N =
      Principal.PushforwardSection.map i U hU ((Scheme.Modules.pushforward f).obj (extension V N))
        (restrictedSection f i U V N ω) :=
  Principal.PushforwardSectionNaturality.map i U hU
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictAdjunction V.ι).unit.app N)) ω

private abbrev ambientRing := Γ(Z, U)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction.ambientRing U
variable {ι : Type u} [LinearOrder ι] (W : ι → Principal.SectionPresheaf.Index U) (c q : ℕ)

def supportedFunctor : ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
  single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} A) (.up ℕ) c ⋙
    Supported.CechHomotopyEquivalence.functor W q

def supportedMap := (supportedFunctor U W c q).map (OpenRestriction.map f i U hU V N)

theorem supported_symbol (ω : Γ((Scheme.Modules.pushforward f).obj N, i ⁻¹ᵁ U)) :
    (supportedFunctor U W c q).map
        (Principal.PushforwardSection.map i U hU ((Scheme.Modules.pushforward f).obj N) ω) ≫
        supportedMap f i U hU V N W c q =
      (supportedFunctor U W c q).map
        (Principal.PushforwardSection.map i U hU ((Scheme.Modules.pushforward f).obj (extension V N))
          (restrictedSection f i U V N ω)) := by
  change (supportedFunctor U W c q).map _ ≫ (supportedFunctor U W c q).map _ = _
  rw [← Functor.map_comp, symbol]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction
