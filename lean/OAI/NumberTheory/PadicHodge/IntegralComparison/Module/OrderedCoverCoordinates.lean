import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.RefinementProjection
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinementQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSource

/-! # Ordered Cover Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.OrderedCoverCoordinates

noncomputable section

/-! The literal ordered coefficient comparison is the original
ordinary affine-cover comparison, through the original projection. -/
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
  (M : X.left.Modules)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

abbrev presheaf := (Affine.HomologyPresheaf.functor R X).obj M
abbrev forget := ModuleCech.CohomologyNaturality.forgetCoefficients R
abbrev projection (q : ℕ) := homologyMap (OrderedCech.Projection.map U (presheaf R X M)) q
abbrev ordinary (q : ℕ) := homologyMap (ModuleCech.CoverRefinement.map R X U V r M) q
abbrev ordered (q : ℕ) := homologyMap (OrderedCech.Refinement.map U V r (presheaf R X M)) q

theorem projection_naturality (q : ℕ) :
    projection R X M U q ≫ ordered R X M U V r q =
      ordinary R X M U V r q ≫ projection R X M V q :=
  OrderedCech.RefinementProjection.homology U V r (presheaf R X M) q

variable [X.left.IsSeparated] [M.IsQuasicoherent]
  (hU : iSup U = ⊤) (hV : iSup V = ⊤)
  (haU : ∀ j, IsAffineOpen (U j)) (haV : ∀ j, IsAffineOpen (V j))

include hU hV haU haV in
omit [LinearOrder ι] [LinearOrder κ] in
theorem ordinary_isIso (q : ℕ) : IsIso (ordinary R X M U V r q) := by
  let := ModuleCech.CoverRefinementQuasiIso.quasiIso R X U V r M hU hV haU haV
  infer_instance

include hU hV haU haV in
theorem ordered_isIso (q : ℕ) : IsIso (ordered R X M U V r q) := by
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (presheaf R X M)) :=
    ModuleCech.CoverRefinementQuasiIso.quasiIso R X U V r M hU hV haU haV
  let := OrderedCech.Refinement.quasiIso U V r (presheaf R X M)
  infer_instance

variable (T : ν → X.left.Opens)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)
  (hT : iSup T = ⊤) (haT : ∀ j, IsAffineOpen (T j))

def comparison (q : ℕ) := by
  letI := ordered_isIso R X M V T rV hV hT haV haT q
  exact Ordered.SingleGlobalSource.coefficientComparison (presheaf R X M) q U V T rU rV

include hU haU in
theorem comparison_coordinates (n : ℕ) :
    (forget R).map (projection R X M U (n+1)) ≫
      (forget R).map (comparison R X M U V hV haV T rU rV hT haT (n+1)) =
    (ModuleCech.Cover.Comparison.iso R X U V hU hV haU haV M n).hom ≫
      (forget R).map (projection R X M V (n+1)) := by
  let := ordinary_isIso R X M V T rV hV hT haV haT (n+1)
  let := ordered_isIso R X M V T rV hV hT haV haT (n+1)
  have h := compare_square (projection R X M U (n+1)) (projection R X M V (n+1))
    (projection R X M T (n+1))
    (ordinary R X M U T rU (n+1)) (ordinary R X M V T rV (n+1))
    (ordered R X M U T rU (n+1)) (ordered R X M V T rV (n+1))
    (projection_naturality R X M U T rU (n+1)) (projection_naturality R X M V T rV (n+1))
  have hm := congrArg (fun a => (forget R).map a) h
  simp only [Functor.map_comp, Functor.map_inv] at hm
  have he : (forget R).map (ordinary R X M U T rU (n+1)) ≫
      inv ((forget R).map (ordinary R X M V T rV (n+1))) =
      (ModuleCech.Cover.Comparison.iso R X U V hU hV haU haV M n).hom := by
    apply (cancel_mono ((forget R).map (ordinary R X M V T rV (n+1)))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [ModuleCech.CoverRefinement.map_eq_coverIso R X U T rU M hU hT haU haT n,
      ModuleCech.CoverRefinement.map_eq_coverIso R X V T rV M hV hT haV haT n]
    simp only [ModuleCech.Cover.Comparison.iso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc]
  rw [he] at hm
  simpa only [comparison, Ordered.SingleGlobalSource.coefficientComparison,
    Functor.map_comp, Functor.map_inv] using hm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.OrderedCoverCoordinates
