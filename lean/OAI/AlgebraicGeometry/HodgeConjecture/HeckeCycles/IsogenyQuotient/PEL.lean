import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualPoincare
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationCancellation

/-! # PEL -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.PEL.CM.Isogeny

noncomputable section

/-! The native IsogenyQuotient isogeny, with its actual represented dual map,
supplies TateComparison's PEL isogeny and uniqueness among all group morphisms.
Universal global functions are preserved by the actual base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {S : Scheme.{0}} {g N n : ℕ} {δ ε : Fin g → ℕ}
  (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S)
  (B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g ε N S)
  (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
  (hB : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions B.polarized.abelian.scheme)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian)

def isogeny
    (hp : f.hom ≫ B.polarized.polarization.isogeny.hom ≫
      AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.polarized.dual B.polarized.dual =
        A.polarized.polarization.isogeny.hom ^ n)
    (ha : ∀ a, A.action.map a ≫ f.hom = f.hom ≫ B.action.map a)
    (hm : ∀ (T : Over S)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (A.polarized.level.hom.app (.op T) c).val ≫ f.hom =
        (B.polarized.level.hom.app (.op T) c).val) :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (PELFamily.CM.Family.ofActionData A) (PELFamily.CM.Family.ofActionData B) n where
  isogeny := f
  dualHom := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.polarized.dual B.polarized.dual
  dualGroup := AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps.Construction.universalFunction_nativeDualMap_isMonHom f.hom A.polarized.dual
    B.polarized.dual
    (AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source B.polarized.polarization.isogeny.hom hB)
  poincare := (AbelianScheme.IsogenyQuotient.UniversalFunction.DualPoincare.Construction.universalFunction_nativeDualMap_poincare
    A.polarized.dual B.polarized.dual hA f.hom).symm
  equivariant a := by
    change AbelianScheme.TateComparison.End.endSchemeMap _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action a) ≫ f.hom =
      f.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap _ (AbelianScheme.TateComparison.PELAdapters.actionToEnd B.action a)
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap, AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap]
    exact ha a
  polarization := hp
  marking := hm

include hB in
omit [NumberField E] [NumberField.IsCMField E] in
theorem polarization_unique
    (hp : f.hom ≫ B.polarized.polarization.isogeny.hom ≫
      AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.polarized.dual B.polarized.dual =
        A.polarized.polarization.isogeny.hom ^ n)
    (p : B.polarized.abelian.scheme ⟶ B.polarized.dual.abelian.scheme)
    [IsMonHom p]
    (heq : f.hom ≫ p ≫
      AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.polarized.dual B.polarized.dual =
        A.polarized.polarization.isogeny.hom ^ n) :
    p = B.polarized.polarization.isogeny.hom :=
  @AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationCancellation.Construction.universalFunction_polarizationPullback_injective S g g
    A.polarized.abelian B.polarized.abelian f A.polarized.dual B.polarized.dual
    hB p B.polarized.polarization.isogeny.hom
    (inferInstanceAs (IsMonHom p)) B.polarized.polarization.isogeny.preservesGroup
    (heq.trans hp.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.PEL.CM.Isogeny
