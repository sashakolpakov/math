import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IdempotentCoordinateGroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Group Retract Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupRetractPoints.CM

noncomputable section

/-! A scheme-theoretic group retraction gives genuine retractions on
test points and on native multiplicative characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

universe u
variable {S : Scheme.{u}} {A B : Grp (Over S)} (s : B ⟶ A) (r : A ⟶ B)
  (hsr : s ≫ r = 𝟙 B)

include hsr in
theorem points_retraction (T : Over S) (x : T ⟶ B.X) :
    Picard.PoincareBundle.Kernel.Scheme.pointsMap r.hom.hom T (Picard.PoincareBundle.Kernel.Scheme.pointsMap s.hom.hom T x) = x := by
  have h : s.hom.hom ≫ r.hom.hom = 𝟙 B.X := congrArg (fun f : B ⟶ B => f.hom.hom) hsr
  exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) h).trans (Category.comp_id x))

def precomposeCharacters {G H : Grp (Over S)} (f : G ⟶ H) :
    (H ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) →* (G ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) where
  toFun χ := f ≫ χ
  map_one' := MonObj.comp_one f
  map_mul' χ ψ := MonObj.comp_mul f χ ψ

include hsr in
theorem characters_retraction (χ : B ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) :
    precomposeCharacters s (precomposeCharacters r χ) = χ :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ χ) hsr).trans (Category.id_comp χ))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupRetractPoints.CM
