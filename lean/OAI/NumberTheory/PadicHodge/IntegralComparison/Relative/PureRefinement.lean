import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechRefinementConcentration

/-! # Pure Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PureRefinement

noncomputable section

/-! A relative refinement of a pure quasicoherent complex is invertible
once it is invertible on the actual surviving cohomology sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem isIso_of_square {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (f : D ≅ E) (a : A ⟶ D) (b : B ⟶ E) [IsIso b]
    (h : e.hom ≫ b = a ≫ f.hom) : IsIso a := by
  have he : e.hom ≫ b ≫ f.inv = a := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun z => z ≫ f.inv) h
  rw [← he]
  infer_instance

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechRefinementConcentration
variable {X : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V)
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q) (q : ℕ)
  [hiso : IsIso (RelativeCech.Refinement.homology U V W r
    (AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj (K.homology c))) q)]

include hU hV hW c hK hiso in
theorem isIso : IsIso (RelativeCech.Refinement.homology U V W r (AdditiveCechConcentration.coefficients K) q) := by
  let b := RelativeCech.Refinement.homology U V W r
    (AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj (K.homology c))) q
  let : IsIso b := hiso
  exact isIso_of_square (AdditiveCechConcentration.iso U hU V hV K c hK q) (AdditiveCechConcentration.iso U hU W hW K c hK q) _ b
    (AdditiveCechRefinementConcentration.refinement_square U hU V hV W hW r K c hK q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PureRefinement
