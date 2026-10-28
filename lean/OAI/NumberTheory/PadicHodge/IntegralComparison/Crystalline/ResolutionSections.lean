import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceAcyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactInjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafResolutionSections

/-! # Resolution Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionSections

noncomputable section

/-!
# IntegralComparison: actual crystalline injective resolutions are exact on affine sections

Restriction of an actual injective resolution to any crystalline slice
remains an injective resolution. The proved vanishing of positive
structure-sheaf cohomology on that slice makes its sections exact.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k)))
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))
  (U : BigCrystallineSite.Object p (WittVector p k) J δ f)

def sliceResolution : InjectiveResolution (SliceStructure.structureSheaf U) :=
  ExactInjectiveResolution.map (SliceImage.restriction f U) I

theorem sections_exact_succ (n : ℕ)
    (x : (I.cocomplex.X (n + 1)).obj.obj (op U))
    (hx : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op U) x = 0) :
    ∃ y : (I.cocomplex.X n).obj.obj (op U),
      (I.cocomplex.d n (n + 1)).hom.app (op U) y = x := by
  have := SliceAcyclicity.positive_cohomology_zero p k U n
  exact Module.SheafResolutionSections.exact_succ
    (BigCrystallineSite.Object.topology.over U) (ExactRestriction.Coeff (B := WittVector p k)) (Over.mkIdTerminal (X := U))
    (sliceResolution p k f I U) n x hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionSections
