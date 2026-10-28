import OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale

/-! # Affine Field Restriction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AffineFieldRestriction.Construction

noncomputable section

/-! Affine test algebras for field extension. Restricting scalars
retains the actual underlying test scheme and its structural map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

def restrictFieldAlgebra (R : CommAlgCat.{u} k') : CommAlgCat.{u} k := by
  letI : Algebra k R := Algebra.compHom R (algebraMap k k')
  exact CommAlgCat.of k R

def restrictFieldAlgebraMap {R S : CommAlgCat.{u} k'} (a : R ⟶ S) :
    restrictFieldAlgebra (k := k) R ⟶ restrictFieldAlgebra (k := k) S := by
  letI : Algebra k R := Algebra.compHom R (algebraMap k k')
  letI : Algebra k S := Algebra.compHom S (algebraMap k k')
  exact CommAlgCat.ofHom {
    toRingHom := a.hom.toRingHom
    commutes' x := by
      change a.hom (algebraMap k' R (algebraMap k k' x)) =
        algebraMap k' S (algebraMap k k' x)
      exact a.hom.commutes _ }

def restrictFieldAlgebras : CommAlgCat.{u} k' ⥤ CommAlgCat.{u} k where
  obj R := restrictFieldAlgebra R
  map a := restrictFieldAlgebraMap a
  map_id R := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  map_comp a b := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl

theorem specMap_ringHom_comp {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    Spec.map (CommRingCat.ofHom (g.hom.comp f.hom)) = Spec.map g ≫ Spec.map f :=
  Spec.map_comp f g

theorem restrictedAffine_structure (R : CommAlgCat.{u} k') :
    (GroupSchemes.FiniteEtale.affine k (restrictFieldAlgebra (k := k) R)).hom =
      (GroupSchemes.FiniteEtale.affine k' R).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k')) :=
  specMap_ringHom_comp (CommRingCat.ofHom (algebraMap k k'))
    (CommRingCat.ofHom (algebraMap k' R))

def overIsoOfStructureEq {S X : Scheme.{u}} (f g : X ⟶ S) (h : g = f) :
    Over.mk f ≅ Over.mk g :=
  Over.isoMk (Iso.refl X) ((Category.id_comp g).trans h)

theorem overIsoOfStructureEq_hom_left {S X : Scheme.{u}} (f g : X ⟶ S) (h : g = f) :
    (overIsoOfStructureEq f g h).hom.left = 𝟙 X := rfl

def restrictedAffineBaseIso (R : CommAlgCat.{u} k') :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj (GroupSchemes.FiniteEtale.affine k' R) ≅
      GroupSchemes.FiniteEtale.affine k (restrictFieldAlgebra (k := k) R) :=
  overIsoOfStructureEq
    ((GroupSchemes.FiniteEtale.affine k' R).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
    (GroupSchemes.FiniteEtale.affine k (restrictFieldAlgebra (k := k) R)).hom
    (restrictedAffine_structure (k := k) R)

theorem restrictedAffineBaseIso_naturality {R S : CommAlgCat.{u} k'} (a : R ⟶ S) :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k')))).map
        ((algSpec (.of k')).map a.op) ≫ (restrictedAffineBaseIso (k := k) R).hom =
      (restrictedAffineBaseIso (k := k) S).hom ≫
        (algSpec (.of k)).map (restrictFieldAlgebraMap (k := k) a).op := by
  apply Over.OverMorphism.ext
  change (Spec.map (CommRingCat.ofHom a.hom.toRingHom)) ≫ 𝟙 _ =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom a.hom.toRingHom)
  rw [Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AffineFieldRestriction.Construction
