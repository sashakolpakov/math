import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativePureLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementTransfer

/-! # Relative Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeTransfer

noncomputable section

/-! The exact original principal right/inverse-left resolution map
agrees with its relative Čech map, including the canonical supported input class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U) (q : ℕ)

def transformation : RelativeConcentration.linearFunctor U hU W q ⟶ RelativeConcentration.relativeFunctor U hU W q where
  app K := (RelativeConcentration.comparison U hU W K q).hom
  naturality _ _ a := RelativeConcentration.naturality U hU W a q

variable {P K T : CochainComplex X.Modules ℕ}
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (T.X q).IsQuasicoherent]
  (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T)

include hU in
omit [X.IsSeparated] in
theorem left_isIso : IsIso ((PrincipalReference.Concentration.Reference.functor U hU W q).map l) :=
  PrincipalReference.Concentration.Reference.supported_isIso U hU W l q

def map := by
  letI := left_isIso U hU W q l
  exact IntegralComparison.Functor.RefinementMap.map (PrincipalReference.Concentration.Reference.functor U hU W q) l a

abbrev relativeMap := RelativeCech.RefinementTransfer.map (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
  (RelativeConcentration.family U hU W) (RelativeConcentration.family_affine U hU W) q l a

@[reassoc]
theorem comparison_map : (AdditiveSections.forgetScalars U).map (RelativeTransfer.map U hU W q l a) ≫
    (RelativeConcentration.comparison U hU W K q).hom = (RelativeConcentration.comparison U hU W P q).hom ≫ relativeMap U hU W q l a := by
  let := left_isIso U hU W q l
  let : IsIso ((RelativeConcentration.linearFunctor U hU W q).map l) := by
    change IsIso ((AdditiveSections.forgetScalars U).map ((PrincipalReference.Concentration.Reference.functor U hU W q).map l))
    infer_instance
  let := RelativeCech.RefinementTransfer.left_isIso (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
    (RelativeConcentration.family U hU W) (RelativeConcentration.family_affine U hU W) q l
  have h := IntegralComparison.Functor.RefinementMap.naturality (RelativeConcentration.linearFunctor U hU W q)
    (RelativeConcentration.relativeFunctor U hU W q) (transformation U hU W q) l a
  simpa only [RelativeTransfer.map, IntegralComparison.Functor.RefinementMap.map, Functor.map_comp, Functor.map_inv]

variable [∀ q, (P.X q).IsQuasicoherent] (c : ℕ) (hP : ∀ k, k ≠ c → P.ExactAt k)
  (f : Z ⟶ X) [IsClosedImmersion f] (N : Z.Modules)
  (e : P.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hW : ∀ i, SectionPresheaf.openSubset U (W i) ≤ SectionIdealPuncturedCover.outside f.ker)

include hW in
theorem localized_map :
    (PrincipalReference.SupportedClass.Reference.localize U hU W P c hP f N e hW q ≫
      (AdditiveSections.forgetScalars U).map (RelativeTransfer.map U hU W q l a)) ≫ (RelativeConcentration.comparison U hU W K q).hom =
    Relative.SupportedPureClass.lift (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
      (RelativeConcentration.family U hU W) (RelativeConcentration.family_affine U hU W) P c hP f N e hW q ≫ relativeMap U hU W q l a := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (PrincipalReference.SupportedClass.Reference.localize U hU W P c hP f N e hW q ≫ ·)
      (comparison_map U hU W q l a)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ relativeMap U hU W q l a)
          (RelativePureLift.comparison_lift U hU W P c hP f N e hW q))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeTransfer
