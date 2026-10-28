import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerOrbitEq
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Geometric Points Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricPointsOf.Construction.GeometricPoints

/-! A finite set of geometric points detects quasi-finiteness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem finite_space_of_finite_rational_points {K : Type u} [Field K] [IsAlgClosed K]
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [Finite {p : Spec (.of K) ⟶ X.left // p ≫ X.hom = 𝟙 _}] : Finite X.left := by
  have : Finite (closedPoints X.left) := Finite.of_equiv _ (pointEquivClosedPoint X.hom)
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hf : (closedPoints X.left).Finite := Set.toFinite _
  have : DiscreteTopology X.left := JacobsonSpace.discreteTopology hf
  have hu : (Set.univ : Set X.left).Finite := by
    simpa only [closedPoints_eq_univ] using hf
  exact Set.finite_univ_iff.mp hu

theorem locallyQuasiFinite_of_finite_geometric_points {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Y),
      Finite (Over.mk a ⟶ Over.mk f)) : LocallyQuasiFinite f := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  let a : Spec (.of K) ⟶ Y := Spec.map (CommRingCat.ofHom
    (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y
  have : Finite (Over.mk a ⟶ Over.mk f) := h K a
  let P : Over (Spec (.of K)) := Over.mk (pullback.snd f a)
  have : LocallyOfFiniteType P.hom := by dsimp [P]; infer_instance
  have : Finite {p : Spec (.of K) ⟶ P.left // p ≫ P.hom = 𝟙 _} :=
    Finite.of_equiv _ (PowerOrbitEq.Construction.PowerOrbit.fieldPointPullbackEquiv (Over.mk f) a)
  have : Finite P.left := finite_space_of_finite_rational_points P
  have : Finite (pullback f a : Scheme.{u}) := inferInstanceAs (Finite P.left)
  have ha : Set.range a = {y} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact Y.fromSpecResidueField_apply y _
    · intro hz
      change z = y at hz
      subst z
      exact ⟨IsLocalRing.closedPoint K, Y.fromSpecResidueField_apply y _⟩
  have hr := Set.finite_range (pullback.fst f a)
  rwa [Scheme.Pullback.range_fst, ha] at hr

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricPointsOf.Construction.GeometricPoints
