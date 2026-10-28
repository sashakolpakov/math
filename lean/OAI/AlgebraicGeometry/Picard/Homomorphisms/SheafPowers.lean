import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupSheafMaps

/-! # Sheaf Powers -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafPowers

noncomputable section

/-! Power maps commute with commutative-group sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}}

def commGroupPresheafPow (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) (n : ℕ) : P ⟶ P where
  app T := CommGrpCat.ofHom (powMonoidHom n)
  naturality {T U} f := by
    ext x
    exact ((P.map f).hom.map_pow x n).symm

theorem sheafify_commGroupPresheafPow (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) (n : ℕ) :
    sheafifyMap (Scheme.fppfTopology.over S) (commGroupPresheafPow P n) =
      commGroupPresheafPow (sheafify (Scheme.fppfTopology.over S) P) n := by
  apply sheafify_hom_ext _ _ _
    ((presheafToSheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).obj P).property
  rw [← toSheafify_naturality]
  ext T x
  exact ((toSheafify (Scheme.fppfTopology.over S) P).app T).hom.map_pow x n

theorem picardTypeSheafify_pow (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}) (n : ℕ)
    (T : (Over S)ᵒᵖ)
    (x : (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T) :
    (sheafifyMap (Scheme.fppfTopology.over S)
      (Functor.whiskerRight (commGroupPresheafPow P n) (forget CommGrpCat))).app T x = x ^ n := by
  apply (GroupSheafification.Construction.picardTypeSheafifyEquiv P T).injective
  rw [GroupSheafMaps.Construction.picardTypeSheafifyEquiv_map, sheafify_commGroupPresheafPow]
  exact (map_pow (GroupSheafification.Construction.picardTypeSheafifyMulEquiv P T) x n).symm

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafPowers
