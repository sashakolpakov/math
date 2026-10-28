import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.FunctorConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Concentration

/-! # Concentration Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ConcentrationSingle

noncomputable section

/-! The original sheaf concentration, after principal sections,
respects every genuine cochain map to a single presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (N : (SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U))
  (a : ((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj K ⟶
    (single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) (.up ℕ) c).obj N)

theorem map_to_single (q : ℕ) :
    (Supported.CechHomotopyEquivalence.functor W q).map a =
      (PrincipalReference.Concentration.Reference.iso U hU W K c hK q).hom ≫
        (Supported.CechHomotopyEquivalence.functor W q).map
          ((singleMapHomologicalComplex (ModuleFunctor.functor U hU)
            (.up ℕ) c).hom.app (K.homology c)) ≫
          (Supported.CechHomotopyEquivalence.functor W q).map
            ((single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) (.up ℕ) c).map
              ((ModuleHomology.complexIso U hU K c).inv ≫
                homologyMap a c ≫ (singleObjHomologySelfIso (.up ℕ) c N).hom)) := by
  let (j : ℕ) : ((CohomologyConcentration.truncation K c).X j).IsQuasicoherent :=
    QuasicoherentTruncation.truncation K c j
  let : (K.homology c).IsQuasicoherent := QuasicoherentTruncation.cohomology K c
  let (j : ℕ) : (((single X.Modules (.up ℕ) c).obj (K.homology c)).X j).IsQuasicoherent :=
    QuasicoherentTruncation.single (K.homology c) c j
  let (j : ℕ) : (ModuleFunctor.functor U hU).PreservesLeftHomologyOf (K.sc j) :=
    ModuleQuasiIso.preservesLeft U hU K j
  let (j : ℕ) : (ModuleFunctor.functor U hU).PreservesLeftHomologyOf
      ((CohomologyConcentration.truncation K c).sc j) :=
    ModuleQuasiIso.preservesLeft U hU (CohomologyConcentration.truncation K c) j
  let (j : ℕ) : (ModuleFunctor.functor U hU).PreservesLeftHomologyOf
      (((single X.Modules (.up ℕ) c).obj (K.homology c)).sc j) :=
    ModuleQuasiIso.preservesLeft U hU _ j
  let : IsIso ((((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)) ⋙
      Supported.CechHomotopyEquivalence.functor W q).map (CohomologyConcentration.projection K c)) :=
    PrincipalReference.Concentration.Reference.projection_isIso U hU W K c hK q
  let : IsIso ((((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)) ⋙
      Supported.CechHomotopyEquivalence.functor W q).map (CohomologyConcentration.inclusion K c)) :=
    PrincipalReference.Concentration.Reference.inclusion_isIso U hU W K c hK q
  have hG : ∀ {P Q : CochainComplex ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) ℕ}
      (b : P ⟶ Q), QuasiIso b →
        IsIso ((Supported.CechHomotopyEquivalence.functor W q).map b) := by
    intro P Q b hb
    let := hb
    let := AugmentedOrdered.CechQuasiIso.quasiIso W Γ(X, U) b
    change IsIso (homologyMap (AugmentedOrdered.CechForgetNaturality.map W b) q)
    infer_instance
  exact Mapped.FunctorConcentration.map_to_single
    (ModuleFunctor.functor U hU) K c hK
    (Supported.CechHomotopyEquivalence.functor W q) hG N a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ConcentrationSingle
