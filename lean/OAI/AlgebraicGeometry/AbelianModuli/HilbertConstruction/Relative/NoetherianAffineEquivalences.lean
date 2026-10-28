import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.NoetherianAffineTests

/-! # Noetherian Affine Equivalences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.NoetherianAffineEquivalences

noncomputable section

/-! Natural equivalences on Noetherian affine test points give
actual relative scheme isomorphisms. Inverse naturality follows
from the forward naturality and bijectivity. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure RelativeNoetherianAffineTestEquiv {S : Scheme.{u}} (X Y : Over S) where
  app : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (f : Spec R ⟶ S),
    (Over.mk f ⟶ X) ≃ (Over.mk f ⟶ Y)
  naturality : ∀ (R A : CommRingCat.{u}) [IsNoetherianRing R] [IsNoetherianRing A]
    (f : Spec R ⟶ S) (g : Spec A ⟶ S) (a : Over.mk g ⟶ Over.mk f) (x : Over.mk f ⟶ X),
    app A g (a ≫ x) = a ≫ app R f x

namespace RelativeNoetherianAffineTestEquiv
variable {S : Scheme.{u}} {X Y : Over S} (D : RelativeNoetherianAffineTestEquiv X Y)

def forward : NoetherianAffineTests.RelativeNoetherianAffineTestData X Y where
  app := by
    intro R _ f x
    exact D.app R f x
  naturality := D.naturality

def backward : NoetherianAffineTests.RelativeNoetherianAffineTestData Y X where
  app := by
    intro R _ f y
    exact (D.app R f).symm y
  naturality R A _ _ f g a y := by
    apply (D.app A g).injective
    rw [Equiv.apply_symm_apply, D.naturality, Equiv.apply_symm_apply]

def toIso [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left] : X ≅ Y :=
  D.forward.toIso D.backward
    (by intro R _ f x; exact (D.app R f).symm_apply_apply x)
    (by intro R _ f y; exact (D.app R f).apply_symm_apply y)

theorem toIso_on_affine [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left]
    (R : CommRingCat.{u}) [IsNoetherianRing R] (f : Spec R ⟶ S) (x : Over.mk f ⟶ X) :
    x ≫ D.toIso.hom = D.app R f x := D.forward.toHom_on_affine R f x

end RelativeNoetherianAffineTestEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.NoetherianAffineEquivalences
