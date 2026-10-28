import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.DescentData

/-! # Descent Comparison -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DescentComparison.Construction

noncomputable section

/-!
# Completion: fully faithful algebra descent on the actual affine site

The ordinary faithfully flat comparison recovers every morphism between
weakly étale algebras. Recovery isomorphisms also lift to the site coalgebras.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))

/-- A morphism of the restricted comparison objects is an ordinary descent morphism. -/
def proEtaleComparisonHomForget {A B : Algebras.Construction.ProEtaleAlgebra R}
    (g : (Comonad.comparison (AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf)).obj A ⟶
      (Comonad.comparison (AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf)).obj B) :
    (Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f)).obj A.obj ⟶
      (Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f)).obj B.obj where
  f := g.f.hom
  h := by
    have h := (Algebras.Construction.weaklyEtaleAlgebra S).ι.congr_map g.h
    change (CommBaseChange.Construction.commAlgExtend f).map (((AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).hom) ≫
        (CommBaseChange.Construction.commAlgExtend f).map ((CommBaseChange.Construction.commAlgRestrict f).map g.f.hom) =
      g.f.hom ≫ (CommBaseChange.Construction.commAlgExtend f).map (((AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app B).hom) at h
    rw [AlgebraBaseChange.Construction.proEtaleAlgebraAdj_unit, AlgebraBaseChange.Construction.proEtaleAlgebraAdj_unit] at h
    exact h

/-- Faithfully flat descent recovers all morphisms between actual affine site objects. -/
def proEtaleComparisonFullyFaithful (hflat : f.FaithfullyFlat) :
    (Comonad.comparison (AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf)).FullyFaithful := by
  have : (Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f)).IsEquivalence :=
    (CommFlatDescent.Construction.commAlgComonadic f hflat).eqv
  let ff := Functor.FullyFaithful.ofFullyFaithful
    (Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f))
  exact {
    preimage g := ObjectProperty.homMk (ff.preimage (proEtaleComparisonHomForget f hf g))
    map_preimage g := by
      apply Comonad.Coalgebra.Hom.ext
      apply ObjectProperty.hom_ext
      exact congrArg Comonad.Coalgebra.Hom.f
        (ff.map_preimage (proEtaleComparisonHomForget f hf g))
    preimage_map g := by
      apply ObjectProperty.hom_ext
      exact ff.preimage_map g.hom }

/-- A recovery isomorphism respecting ordinary descent data also respects the site descent data. -/
def proEtaleComparisonIso {A : Algebras.Construction.ProEtaleAlgebra R}
    {D : (AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).toComonad.Coalgebra}
    (e : (Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f)).obj A.obj ≅
      Affine.DescentData.Construction.proEtaleCoalgebraForget f hf D) :
    (Comonad.comparison (AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf)).obj A ≅ D :=
  Comonad.Coalgebra.isoMk
    (ObjectProperty.isoMk _ ((Comonad.forget (CommBaseChange.Construction.commAlgExtendRestrictAdj f).toComonad).mapIso e))
    (by
      apply ObjectProperty.hom_ext
      change (CommBaseChange.Construction.commAlgExtend f).map (((AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).hom) ≫
          (CommBaseChange.Construction.commAlgExtend f).map ((CommBaseChange.Construction.commAlgRestrict f).map e.hom.f) = e.hom.f ≫ D.a.hom
      rw [AlgebraBaseChange.Construction.proEtaleAlgebraAdj_unit]
      exact e.hom.h)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DescentComparison.Construction
