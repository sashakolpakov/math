import OAI.AlgebraicGeometry.FormalGeometry.Completion.Cohomology
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius

/-! # Frobenius -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction

noncomputable section

/-!
# Completion: Frobenius on the geometric fiber

This is the base change of the q-power endomorphism over the finite
ground field. It fixes the algebraically closed base. It is distinct
from the absolute q-power map on the geometric fiber's structure sheaf.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

/-- The geometric point chosen by the algebraic closure. -/
abbrev algebraicClosureBase :
    Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- The geometric fiber with its structure morphism to the algebraic closure. -/
abbrev geometricFiberOver (A : Over (Spec (CommRingCat.of k))) :=
  (Over.pullback (algebraicClosureBase k)).obj A

/-- A morphism over k acts on the actual geometric fibers by base change. -/
def geometricFiberMap {A B : Over (Spec (CommRingCat.of k))} (f : A ⟶ B) :
    Cohomology.Construction.geometricFiber A ⟶ Cohomology.Construction.geometricFiber B :=
  ((Over.pullback (algebraicClosureBase k)).map f).left

theorem geometricFiberMap_comp
    {A B C : Over (Spec (CommRingCat.of k))} (f : A ⟶ B) (g : B ⟶ C) :
    geometricFiberMap k (f ≫ g) = geometricFiberMap k f ≫ geometricFiberMap k g := by
  unfold geometricFiberMap
  rw [CategoryTheory.Functor.map_comp]
  rfl

theorem geometricFiberMap_fst
    {A B : Over (Spec (CommRingCat.of k))} (f : A ⟶ B) :
    geometricFiberMap k f ≫ pullback.fst B.hom (algebraicClosureBase k) =
      pullback.fst A.hom (algebraicClosureBase k) ≫ f.left := by
  exact pullback.lift_fst _ _ _

theorem geometricFiberMap_snd
    {A B : Over (Spec (CommRingCat.of k))} (f : A ⟶ B) :
    geometricFiberMap k f ≫ pullback.snd B.hom (algebraicClosureBase k) =
      pullback.snd A.hom (algebraicClosureBase k) := by
  exact pullback.lift_snd _ _ _

variable [Fintype k]

/-- The Frobenius morphism whose pullback on geometric H¹ occurs in Completion. -/
def geometricSchemeFrobenius (A : Over (Spec (CommRingCat.of k))) :
    Cohomology.Construction.geometricFiber A ⟶ Cohomology.Construction.geometricFiber A :=
  geometricFiberMap k (Frobenius.Construction.finiteFieldSchemeFrobenius k A)

theorem geometricSchemeFrobenius_over (A : Over (Spec (CommRingCat.of k))) :
    geometricSchemeFrobenius k A ≫ (geometricFiberOver k A).hom =
      (geometricFiberOver k A).hom :=
  geometricFiberMap_snd k (Frobenius.Construction.finiteFieldSchemeFrobenius k A)

theorem geometricSchemeFrobenius_naturality
    {A B : Over (Spec (CommRingCat.of k))} (f : A ⟶ B) :
    geometricSchemeFrobenius k A ≫ geometricFiberMap k f =
      geometricFiberMap k f ≫ geometricSchemeFrobenius k B := by
  unfold geometricSchemeFrobenius
  rw [← geometricFiberMap_comp, Frobenius.Construction.finiteFieldSchemeFrobenius_naturality,
    geometricFiberMap_comp]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction
