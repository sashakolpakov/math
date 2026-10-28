import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Noetherian -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian

/-! The product schemes used by descent are locally Noetherian under the actual finite-type hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} (A B : Over S)
  [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]

theorem product_finiteType : LocallyOfFiniteType (A ⊗ B).hom := by
  dsimp
  infer_instance

theorem product_noetherian [IsLocallyNoetherian S] : IsLocallyNoetherian (A ⊗ B).left := by
  have : LocallyOfFiniteType (A ⊗ B).hom := product_finiteType A B
  exact LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Noetherian
