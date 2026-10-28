import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.OrderedCoverCoordinates

/-! # Linear Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.LinearCover.Comparison

noncomputable section

/-! The original affine-cover comparison before forgetting the
module structure, with its ordinary and ordered coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compare_square {C : Type*} [Category C]
    {A B T A' B' T' : C} (p : A ⟶ A') (q : B ⟶ B') (s : T ⟶ T')
    (a : A ⟶ T) (b : B ⟶ T) (a' : A' ⟶ T') (b' : B' ⟶ T')
    [IsIso b] [IsIso b'] (ha : p ≫ a' = a ≫ s) (hb : q ≫ b' = b ≫ s) :
    p ≫ (a' ≫ inv b') = (a ≫ inv b) ≫ q := by
  apply (cancel_mono b').mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hb, IsIso.inv_hom_id_assoc]
  exact ha

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [X.left.IsSeparated] (M : X.left.Modules) [M.IsQuasicoherent]
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (T : ν → X.left.Opens)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)
  (hT : iSup T = ⊤) (haT : ∀ j, IsAffineOpen (T j))

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.OrderedCoverCoordinates

def comparison (q : ℕ) :
    (DimensionBound.complex R X M U).homology q ⟶
      (DimensionBound.complex R X M V).homology q := by
  letI := Module.OrderedCoverCoordinates.ordinary_isIso R X M V T rV hV hT haV haT q
  exact Module.OrderedCoverCoordinates.ordinary R X M U T rU q ≫ inv (Module.OrderedCoverCoordinates.ordinary R X M V T rV q)

theorem projection_square (q : ℕ) :
    Module.OrderedCoverCoordinates.projection R X M U q ≫
      Module.OrderedCoverCoordinates.comparison R X M U V hV haV T rU rV hT haT q =
    comparison R X M U V hV haV T rU rV hT haT q ≫ Module.OrderedCoverCoordinates.projection R X M V q := by
  let := Module.OrderedCoverCoordinates.ordinary_isIso R X M V T rV hV hT haV haT q
  let := Module.OrderedCoverCoordinates.ordered_isIso R X M V T rV hV hT haV haT q
  exact compare_square (Module.OrderedCoverCoordinates.projection R X M U q) (Module.OrderedCoverCoordinates.projection R X M V q)
    (Module.OrderedCoverCoordinates.projection R X M T q)
    (Module.OrderedCoverCoordinates.ordinary R X M U T rU q) (Module.OrderedCoverCoordinates.ordinary R X M V T rV q)
    (Module.OrderedCoverCoordinates.ordered R X M U T rU q) (Module.OrderedCoverCoordinates.ordered R X M V T rV q)
    (Module.OrderedCoverCoordinates.projection_naturality R X M U T rU q) (Module.OrderedCoverCoordinates.projection_naturality R X M V T rV q)

variable (hU : iSup U = ⊤) (haU : ∀ j, IsAffineOpen (U j))

include hU haU in
omit [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] in
theorem comparison_isIso (q : ℕ) :
    IsIso (comparison R X M U V hV haV T rU rV hT haT q) := by
  let := Module.OrderedCoverCoordinates.ordinary_isIso R X M U T rU hU hT haU haT q
  let := Module.OrderedCoverCoordinates.ordinary_isIso R X M V T rV hV hT haV haT q
  dsimp only [comparison]
  infer_instance

omit [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] in
theorem forget_eq (n : ℕ) :
    (Module.OrderedCoverCoordinates.forget R).map (comparison R X M U V hV haV T rU rV hT haT (n+1)) =
      (Cover.Comparison.iso R X U V hU hV haU haV M n).hom := by
  let := Module.OrderedCoverCoordinates.ordinary_isIso R X M V T rV hV hT haV haT (n+1)
  dsimp only [comparison]
  rw [Functor.map_comp, Functor.map_inv]
  apply (cancel_mono ((Module.OrderedCoverCoordinates.forget R).map (Module.OrderedCoverCoordinates.ordinary R X M V T rV (n+1)))).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [CoverRefinement.map_eq_coverIso R X U T rU M hU hT haU haT n,
    CoverRefinement.map_eq_coverIso R X V T rV M hV hT haV haT n]
  simp only [Cover.Comparison.iso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.LinearCover.Comparison
