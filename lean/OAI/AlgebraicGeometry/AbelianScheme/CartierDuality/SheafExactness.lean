import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafQuotients
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Sheaf Exactness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafExactness

noncomputable section

/-!
# CartierDuality: exactness in commutative fppf sheaves in multiplicative notation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

namespace Construction.CommutativeSheaves

/-- The additive notation for the group of homomorphisms, retaining
the concrete trivial homomorphism as zero. -/
def commGrpHomEquiv (X Y : CommGrpCat.{u}) : (X ⟶ Y) ≃ Additive (X →* Y) where
  toFun f := Additive.ofMul f.hom
  invFun f := CommGrpCat.ofHom f.toMul
  left_inv _ := rfl
  right_inv _ := rfl

/-- Homomorphisms of commutative groups add by pointwise multiplication.
The zero maps agree definitionally with the existing trivial maps. -/
instance commGrpPreadditive : Preadditive CommGrpCat.{u} where
  homGroup X Y := (commGrpHomEquiv X Y).addCommGroup
  add_comp X Y Z f f' g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact g.hom.map_mul (f x) (f' x)
  comp_add X Y Z f g g' := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    rfl

/-- Commutative groups form an abelian category in multiplicative notation. -/
instance commGrpAbelian : Abelian CommGrpCat.{u} :=
  abelianOfEquivalence commGroupAddCommGroupEquivalence.functor

end Construction.CommutativeSheaves

namespace Construction.Schemes

/-- The actual commutative fppf-sheaf category is abelian. -/
instance fppfAbAbelian (S : Scheme.{u}) : Abelian (CommutativeSheavesAb.Construction.Schemes.FppfAb S) := inferInstance

/-- Every sheaf epimorphism is normal for the concrete trivial zero maps. -/
instance fppfAbNormalEpi (S : Scheme.{u}) : IsNormalEpiCategory (CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
  @Abelian.toIsNormalEpiCategory (CommutativeSheavesAb.Construction.Schemes.FppfAb S) inferInstance (fppfAbAbelian S)

/-- Every sheaf monomorphism is normal for the concrete trivial zero maps. -/
instance fppfAbNormalMono (S : Scheme.{u}) : IsNormalMonoCategory (CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
  @Abelian.toIsNormalMonoCategory (CommutativeSheavesAb.Construction.Schemes.FppfAb S) inferInstance (fppfAbAbelian S)

/-- Short complexes of the actual commutative fppf sheaves have homology. -/
instance fppfAbWithHomology (S : Scheme.{u}) : CategoryWithHomology (CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
  @categoryWithHomology_of_abelian (CommutativeSheavesAb.Construction.Schemes.FppfAb S) inferInstance (fppfAbAbelian S)

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafExactness
