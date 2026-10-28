import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Multiplication Fixed Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationFixedMap

noncomputable section

/-!
# Restrict the fixed coordinate of a genuine fiberwise line multiplication
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {E A X Z : Over S} [GrpObj A]
  (p : E ⟶ A) (r : E ⟶ X) (φ : X ⟶ Z)

/-- Equal fixed coordinates have equal images under any actual scheme morphism. -/
theorem mappedRel {T : Over S} (a b c : T ⟶ E) (h : FiberwiseMultiplication.ProductRel p r a b c) :
    FiberwiseMultiplication.ProductRel p (r ≫ φ) a b c := by
  refine ⟨h.1, ?_, ?_⟩
  · exact (Category.assoc a r φ).symm.trans
      ((congrArg (fun x => x ≫ φ) h.2.1).trans (Category.assoc b r φ))
  · exact (Category.assoc a r φ).symm.trans
      ((congrArg (fun x => x ≫ φ) h.2.2).trans (Category.assoc c r φ))

variable (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p (r ≫ φ) L)

/-- Refining the fixed coordinate constructs the full multiplication, with all original laws. -/
def restrictFixed : FiberwiseMultiplication.Multiplication p r L where
  product := fun {_T} a b c h => D.product a b c (mappedRel p r φ a b c h)
  product_isIso := fun {_T} a b c h => D.product_isIso a b c (mappedRel p r φ a b c h)
  unitFrame := fun {_T} a ha => D.unitFrame a ha
  unit_left := fun {_T} a x ha h U m => D.unit_left a x ha (mappedRel p r φ a x x h) U m
  unit_right := fun {_T} x a ha h U m => D.unit_right x a ha (mappedRel p r φ x a x h) U m
  associative := fun {_T} a b c ab bc d hab hbc had hcd U s t m =>
    D.associative a b c ab bc d (mappedRel p r φ a b ab hab) (mappedRel p r φ b c bc hbc)
      (mappedRel p r φ a bc d had) (mappedRel p r φ ab c d hcd) U s t m
  product_natural := fun {_T _T'} g a b c h a' b' c' h' ha hb hc =>
    D.product_natural g a b c (mappedRel p r φ a b c h) a' b' c' (mappedRel p r φ a' b' c' h') ha hb hc
  unit_natural := fun {_T _T'} g a a' ha ha' hga => D.unit_natural g a a' ha ha' hga

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationFixedMap
