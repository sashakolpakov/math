import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualMaps
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Affine Category -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCategory.Construction

noncomputable section

/-!
# CartierDuality: contravariant equivalence of finite projective Hopf coordinates

The category is a full subcategory of the native commutative Hopf-algebra
category. Its additional hypotheses are precisely finite projectivity and
cocommutativity.
-/

open _root_.CategoryTheory Opposite

universe u

variable (R : Type u) [CommRing R]

def finiteProjectiveCocomm : ObjectProperty (CommHopfAlgCat.{u} R) :=
  fun A => Module.Finite R A ∧ Module.Projective R A ∧ Coalgebra.IsCocomm R A

abbrev FiniteProjectiveHopf := (finiteProjectiveCocomm R).FullSubcategory

instance (A : FiniteProjectiveHopf R) : Module.Finite R A.obj := A.property.1
instance (A : FiniteProjectiveHopf R) : Module.Projective R A.obj := A.property.2.1
instance (A : FiniteProjectiveHopf R) : Coalgebra.IsCocomm R A.obj := A.property.2.2

/-- The dual object has the same finiteness and projectivity properties. -/
def finiteProjectiveHopfDual (A : FiniteProjectiveHopf R) : FiniteProjectiveHopf R :=
  ⟨CommHopfAlgCat.of R (DualAlgebra.Construction.DualCoordinate R A.obj),
    inferInstance, inferInstance, inferInstance⟩

/-- Cartier dualization on finite projective Hopf coordinates. -/
def finiteProjectiveHopfDualFunctor :
    (FiniteProjectiveHopf R)ᵒᵖ ⥤ FiniteProjectiveHopf R where
  obj A := finiteProjectiveHopfDual R A.unop
  map f := ObjectProperty.homMk
    (CommHopfAlgCat.ofHom (DualMaps.Construction.dualCoordinateBialgHom R f.unop.hom.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Bidual evaluation in the native category of Hopf coordinates. -/
def finiteProjectiveHopfBidualIso (A : FiniteProjectiveHopf R) :
    A ≅ finiteProjectiveHopfDual R (finiteProjectiveHopfDual R A) :=
  ObjectProperty.isoMk _ (CommHopfAlgCat.isoMk (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A.obj))

/-- The natural bidual isomorphism records the evaluation map and all
transition-map compatibilities needed for descent. -/
def finiteProjectiveHopfBidualNatIso :
    𝟭 (FiniteProjectiveHopf R) ≅
      (finiteProjectiveHopfDualFunctor R).rightOp ⋙ finiteProjectiveHopfDualFunctor R :=
  NatIso.ofComponents (finiteProjectiveHopfBidualIso R) (by
    intro A B f
    apply ObjectProperty.hom_ext
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro x
    rfl)

/-- The duality is fully faithful. -/
def finiteProjectiveHopfDual_fullyFaithful :
    (finiteProjectiveHopfDualFunctor R).FullyFaithful where
  preimage {A B} f := (ObjectProperty.homMk
    (CommHopfAlgCat.ofHom
      ((DualMaps.Construction.dualCoordinateBialgHomEquiv R).symm f.hom.hom))).op
  map_preimage f := by
    apply ObjectProperty.hom_ext
    apply CommHopfAlgCat.hom_ext
    exact (DualMaps.Construction.dualCoordinateBialgHomEquiv R).apply_symm_apply f.hom.hom
  preimage_map f := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommHopfAlgCat.hom_ext
    exact (DualMaps.Construction.dualCoordinateBialgHomEquiv R).symm_apply_apply f.unop.hom.hom

instance : (finiteProjectiveHopfDualFunctor R).Full :=
  (finiteProjectiveHopfDual_fullyFaithful R).full
instance : (finiteProjectiveHopfDualFunctor R).Faithful :=
  (finiteProjectiveHopfDual_fullyFaithful R).faithful

instance : (finiteProjectiveHopfDualFunctor R).EssSurj where
  mem_essImage A := ⟨op (finiteProjectiveHopfDual R A),
    ⟨(finiteProjectiveHopfBidualIso R A).symm⟩⟩

instance : (finiteProjectiveHopfDualFunctor R).IsEquivalence where

/-- Cartier duality is a contravariant equivalence for finite projective
commutative, cocommutative Hopf algebras over any commutative ring. -/
def finiteProjectiveHopfDualEquivalence :
    (FiniteProjectiveHopf R)ᵒᵖ ≌ FiniteProjectiveHopf R :=
  (finiteProjectiveHopfDualFunctor R).asEquivalence

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCategory.Construction
