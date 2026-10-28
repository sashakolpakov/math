import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.AlgebraBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CorepresentableDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CommDescentObject

/-! # Descent Data -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.DescentData.Construction

noncomputable section

/-!
# Completion: descent of algebra representatives from the actual affine site

The canonical coaction on a corepresentative in weakly étale algebras gives
a coaction in all commutative algebras, and hence a descended algebra over
the original ring when the covering ring map is faithfully flat.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))

/-- Forgetting the site condition preserves the actual descent coaction and its laws. -/
def proEtaleCoalgebraForget (D : (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).toComonad.Coalgebra) :
    (CommBaseChange.Construction.commAlgExtendRestrictAdj f).toComonad.Coalgebra where
  A := D.A.obj
  a := D.a.hom
  counit := by
    have h := (ProEtale.Algebras.Construction.weaklyEtaleAlgebra S).ι.congr_map D.counit
    change D.a.hom ≫ ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).counit.app D.A).hom = 𝟙 D.A.obj at h
    rw [ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj_counit] at h
    exact h
  coassoc := by
    have h := (ProEtale.Algebras.Construction.weaklyEtaleAlgebra S).ι.congr_map D.coassoc
    change D.a.hom ≫ (CommBaseChange.Construction.commAlgExtend f).map
        (((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf).obj D.A)).hom) =
      D.a.hom ≫ (CommBaseChange.Construction.commAlgExtend f).map ((CommBaseChange.Construction.commAlgRestrict f).map D.a.hom) at h
    rw [ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj_unit] at h
    exact h

variable (F : ProEtale.Algebras.Construction.ProEtaleAlgebra R ⥤ Type w) {Y : ProEtale.Algebras.Construction.ProEtaleAlgebra S}
  (rep : (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf ⋙ F).CorepresentableBy Y)

/-- The canonical actual commutative-algebra descent data of the local representative. -/
def affineRepresentativeCoalgebra : (CommBaseChange.Construction.commAlgExtendRestrictAdj f).toComonad.Coalgebra :=
  proEtaleCoalgebraForget f hf (CorepresentableDescent.Construction.corepresentableDescentCoalgebra (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf) F rep)

variable (hflat : f.FaithfullyFlat)

/-- The descended algebra of a local affine representative. -/
def affineRepresentativeDescended : CommAlgCat.{u} R :=
  CommDescentObject.Construction.descendedCommAlgebra f hflat (affineRepresentativeCoalgebra f hf F rep)

/-- Actual base change recovers the local affine algebra representative. -/
def affineRepresentativeDescendedIso :
    (CommBaseChange.Construction.commAlgExtend f).obj (affineRepresentativeDescended f hf F rep hflat) ≅ Y.obj :=
  CommDescentObject.Construction.descendedCommAlgebraIso f hflat (affineRepresentativeCoalgebra f hf F rep)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.DescentData.Construction
