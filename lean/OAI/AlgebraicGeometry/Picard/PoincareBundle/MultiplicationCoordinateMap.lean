import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Multiplication Coordinate Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinateMap

noncomputable section

/-!
# Restrict an actual fiberwise multiplication along a homomorphism of its group coordinate
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {E A Z X : Over S} [GrpObj A] [GrpObj Z]
  (p : E ⟶ A) (r : E ⟶ X) (φ : A ⟶ Z) [IsMonHom φ]

/-- A homomorphism carries the genuine coordinate product relation to the image-coordinate relation. -/
theorem mappedRel {T : Over S} (a b c : T ⟶ E) (h : FiberwiseMultiplication.ProductRel p r a b c) :
    FiberwiseMultiplication.ProductRel (p ≫ φ) r a b c := by
  refine ⟨?_, h.2⟩
  have he := congrArg (fun x => x ≫ φ) h.1
  rw [MonObj.mul_comp] at he
  simpa only [Category.assoc] using he

/-- A homomorphism carries the genuine unit-coordinate condition to the image coordinate. -/
theorem mappedUnit {T : Over S} (a : T ⟶ E) (ha : a ≫ p = 1) : a ≫ (p ≫ φ) = 1 := by
  rw [← Category.assoc, ha, MonObj.one_comp]

variable (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication (p ≫ φ) r L)

/-- All multiplication laws for the source group coordinate are derived from the actual image-coordinate multiplication. -/
def restrictCoordinate : FiberwiseMultiplication.Multiplication p r L where
  product := fun {_T} a b c h => D.product a b c (mappedRel p r φ a b c h)
  product_isIso := fun {_T} a b c h => D.product_isIso a b c (mappedRel p r φ a b c h)
  unitFrame := fun {_T} a ha => D.unitFrame a (mappedUnit p φ a ha)
  unit_left := fun {_T} a x ha h U m => D.unit_left a x (mappedUnit p φ a ha) (mappedRel p r φ a x x h) U m
  unit_right := fun {_T} x a ha h U m => D.unit_right x a (mappedUnit p φ a ha) (mappedRel p r φ x a x h) U m
  associative := fun {_T} a b c ab bc d hab hbc had hcd U s t m =>
    D.associative a b c ab bc d (mappedRel p r φ a b ab hab) (mappedRel p r φ b c bc hbc)
      (mappedRel p r φ a bc d had) (mappedRel p r φ ab c d hcd) U s t m
  product_natural := fun {_T _T'} g a b c h a' b' c' h' ha hb hc =>
    D.product_natural g a b c (mappedRel p r φ a b c h) a' b' c' (mappedRel p r φ a' b' c' h') ha hb hc
  unit_natural := fun {_T _T'} g a a' ha ha' hga =>
    D.unit_natural g a a' (mappedUnit p φ a ha) (mappedUnit p φ a' ha') hga

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinateMap
