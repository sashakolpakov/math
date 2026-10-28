import OAI.AlgebraicGeometry.FormalGeometry.Completion.CommFlatDescent

/-! # Comm Descent Object -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CommDescentObject.Construction

noncomputable section

/-!
# Completion: the descended commutative algebra and its base-change isomorphism

The descended algebra is obtained from the proved comparison equivalence.
Its base change is isomorphic to the given algebra, respecting its coaction.
-/

open _root_.CategoryTheory Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FaithfullyFlat)

/-- The actual category equivalence supplied by faithfully flat descent. -/
def commAlgDescentEquivalence :
    CommAlgCat.{u} R ≌ (CommBaseChange.Construction.commAlgExtendRestrictAdj f).toComonad.Coalgebra := by
  have : (Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f)).IsEquivalence :=
    (CommFlatDescent.Construction.commAlgComonadic f hf).eqv
  exact (Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f)).asEquivalence

variable (D : (CommBaseChange.Construction.commAlgExtendRestrictAdj f).toComonad.Coalgebra)

/-- The algebra over the original ring constructed by descent. -/
def descendedCommAlgebra : CommAlgCat.{u} R :=
  (commAlgDescentEquivalence f hf).inverse.obj D

/-- The descended algebra recovers the given data as a coalgebra. -/
def descendedCommAlgebraCounit :
    (Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f)).obj (descendedCommAlgebra f hf D) ≅ D :=
  (commAlgDescentEquivalence f hf).counitIso.app D

/-- Tensoring the descended algebra with the covering ring recovers the local algebra. -/
def descendedCommAlgebraIso :
    (CommBaseChange.Construction.commAlgExtend f).obj (descendedCommAlgebra f hf D) ≅ D.A :=
  (Comonad.forget (CommBaseChange.Construction.commAlgExtendRestrictAdj f).toComonad).mapIso
    (descendedCommAlgebraCounit f hf D)

/-- The recovery isomorphism respects the actual coaction, not just the underlying algebra. -/
theorem descendedCommAlgebraIso_coaction :
    ((Comonad.comparison (CommBaseChange.Construction.commAlgExtendRestrictAdj f)).obj (descendedCommAlgebra f hf D)).a ≫
      (CommBaseChange.Construction.commAlgExtendRestrictAdj f).toComonad.map (descendedCommAlgebraIso f hf D).hom =
        (descendedCommAlgebraIso f hf D).hom ≫ D.a :=
  (descendedCommAlgebraCounit f hf D).hom.h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CommDescentObject.Construction
