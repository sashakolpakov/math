import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite Geometric Points -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints

noncomputable section

/-! Finiteness detected by geometric points, retaining the scheme structure
when properness turns quasi-finiteness into finiteness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

def overPointsEquiv {S : Scheme.{u}} (T : Over S)
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ S) :
    (Over.mk s ⟶ T) ≃ {x : Spec (.of k) ⟶ T.left // x ≫ T.hom = s} where
  toFun x := ⟨x.left, x.w⟩
  invFun x := Over.homMk x.val x.property
  left_inv x := by apply Over.OverMorphism.ext; rfl
  right_inv x := rfl

theorem finite_overPoints {S : Scheme.{u}} (T : Over S) [IsFinite T.hom]
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) :
    Finite (Over.mk s ⟶ T) := by
  have := AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.finite_geometric_lifts T.hom s
  exact Finite.of_equiv _ (overPointsEquiv T s).symm

theorem finite_scheme_of_finite_closedPoints (X : Scheme.{u}) [JacobsonSpace X]
    [Finite (closedPoints X)] : Finite X := by
  have hfin : (closedPoints X).Finite := Set.toFinite _
  have : DiscreteTopology X := JacobsonSpace.discreteTopology hfin
  apply Set.finite_univ_iff.mp
  simpa only [closedPoints_eq_univ] using hfin

def rationalPointsClosedEquiv {k : Type u} [Field k] [IsAlgClosed k]
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom] :
    (Over.mk (𝟙 (Spec (.of k))) ⟶ T) ≃ closedPoints T.left :=
  (overPointsEquiv T (𝟙 _)).trans (pointEquivClosedPoint T.hom)

theorem finite_scheme_of_finite_rationalPoints {k : Type u} [Field k] [IsAlgClosed k]
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ T)] : Finite T.left := by
  have : Finite (closedPoints T.left) := Finite.of_equiv _ (rationalPointsClosedEquiv T)
  have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  exact finite_scheme_of_finite_closedPoints T.left

theorem finite_morphism_of_proper_finite_rationalPoints {k : Type u} [Field k] [IsAlgClosed k]
    (T : Over (Spec (.of k))) [IsProper T.hom]
    [Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ T)] : IsFinite T.hom := by
  have : Finite T.left := finite_scheme_of_finite_rationalPoints T
  have : LocallyQuasiFinite T.hom :=
    LocallyQuasiFinite.of_finite_preimage_singleton T.hom (fun _ => Set.toFinite _)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite T.hom).mpr ⟨inferInstance, inferInstance⟩

def geometricResiduePoint (Y : Scheme.{u}) (y : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
    Y.fromSpecResidueField y

theorem geometricResiduePoint_range (Y : Scheme.{u}) (y : Y) :
    Set.range (geometricResiduePoint Y y) = {y} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact Y.fromSpecResidueField_apply y _
  · intro hz
    have hz' : z = y := hz
    subst z
    exact ⟨IsLocalRing.closedPoint _, Y.fromSpecResidueField_apply y _⟩

theorem finite_preimage_of_finite_geometric_lifts {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    [Finite {x : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ X //
      x ≫ f = geometricResiduePoint Y y}] : (f ⁻¹' {y}).Finite := by
  let a := geometricResiduePoint Y y
  let p := pullback.snd f a
  have : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (pullback.snd f a))
  have : Finite (closedPoints (pullback f a : Scheme.{u})) :=
    Finite.of_equiv _ ((AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.geometricLiftSectionEquiv f a).trans (pointEquivClosedPoint p))
  have : JacobsonSpace (pullback f a : Scheme.{u}) := LocallyOfFiniteType.jacobsonSpace p
  have : Finite (pullback f a : Scheme.{u}) := finite_scheme_of_finite_closedPoints _
  have h := Set.finite_range (pullback.fst f a)
  rwa [Scheme.Pullback.range_fst, geometricResiduePoint_range] at h

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints
