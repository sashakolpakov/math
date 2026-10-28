import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalSchemeCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalAlgebraCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocyclePoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfScalarsOf

/-! # Scheme Cocycle Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleCoordinates

noncomputable section

/-! Affine coordinates of a natural regular cocycle on a group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CocyclePoints

/-- Coordinate extraction commutes with pullback of actual regular units. -/
theorem coordinate_pullback {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (v : Γ(Spec (.of S), ⊤)ˣ) :
    Units.map f.toMonoidHom (Units.map (Scheme.ΓSpecIso (.of S)).hom.hom.toMonoidHom v) =
      Units.map (Scheme.ΓSpecIso (.of T)).hom.hom.toMonoidHom
        (Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom.toMonoidHom v) := by
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of T)).inv).injective
  have h := AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection_pullback f
    ((Scheme.ΓSpecIso (.of S)).hom (v : Γ(Spec (.of S), ⊤)))
  simpa [AbelianScheme.CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection] using h.symm

variable (k R : Type u) [CommRing k] [CommRing R] [HopfAlgebra k R]
  (C : NaturalSchemeCocycle.NaturalCocycle ((Spec (.of R)).asOver (Spec (.of k))))

/-- Every law is transported from the actual test-scheme cocycle. -/
def algebraCocycle : NaturalAlgebraCocycle.NaturalCocycle k R where
  value {S} _ _ x y := Units.map (Scheme.ΓSpecIso (.of S)).hom.hom.toMonoidHom
    (C.value (Affine.CocyclePoints.point k R S x) (Affine.CocyclePoints.point k R S y))
  natural {S T} _ _ _ _ f x y := by
    have hc := coordinate_pullback f.toRingHom (C.value (Affine.CocyclePoints.point k R S x) (Affine.CocyclePoints.point k R S y))
    have h := C.natural ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of k)))
      (Affine.CocyclePoints.point k R S x) (Affine.CocyclePoints.point k R S y)
    rw [Affine.CocyclePoints.point_natural, Affine.CocyclePoints.point_natural] at h
    exact hc.trans (congrArg (Units.map (Scheme.ΓSpecIso (.of T)).hom.hom.toMonoidHom) h)
  one_left {S} _ _ x := by
    rw [Affine.CocyclePoints.point_one, C.one_left]
    exact (Units.map (Scheme.ΓSpecIso (.of S)).hom.hom.toMonoidHom).map_one
  one_right {S} _ _ x := by
    rw [Affine.CocyclePoints.point_one, C.one_right]
    exact (Units.map (Scheme.ΓSpecIso (.of S)).hom.hom.toMonoidHom).map_one
  symmetric {_} _ _ x y := by rw [C.symmetric]
  cocycle {S} _ _ x y z := by
    rw [Affine.CocyclePoints.point_mul, Affine.CocyclePoints.point_mul]
    let φ := Units.map (Scheme.ΓSpecIso (.of S)).hom.hom.toMonoidHom
    exact (φ.map_mul _ _).symm.trans
      ((congrArg φ (C.cocycle (Affine.CocyclePoints.point k R S x) (Affine.CocyclePoints.point k R S y) (Affine.CocyclePoints.point k R S z))).trans (φ.map_mul _ _))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleCoordinates
