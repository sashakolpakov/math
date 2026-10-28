import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-! # Algebraic Points -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints.Abelian

noncomputable section

/-!
Arithmetic descent of closed and isolated complex points, needed for CMAbelianVariety.
These are general geometric lemmas. They do not assume or establish that
a CM point is closed or isolated in the required enhanced moduli scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The residue field at a closed point of a locally finite-type rational
scheme is a number field. -/
theorem residueField_numberField_of_closed
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed {x}) :
    NumberField (X.residueField x) := by
  let r := Spec.preimage (X.fromSpecResidueField x ≫ f)
  have : CharZero (X.residueField x) :=
    CharZero.of_addMonoidHom r.hom.toAddMonoidHom (by simp) r.hom.injective
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hf : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hr : r.hom.Finite := (IsFinite.SpecMap_iff r).mp (by
    simpa only [r, Spec.map_preimage] using hf)
  have heq : r.hom = algebraMap ℚ (X.residueField x) := Subsingleton.elim _ _
  rw [heq] at hr
  exact { to_finiteDimensional := RingHom.finite_algebraMap.mp hr }

/-- A complex point with closed image in a locally finite-type rational
scheme factors through the spectrum of a number subfield of ℂ. -/
theorem complex_point_descends_of_closed
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (hp : IsClosed {p (IsLocalRing.closedPoint ℂ)}) :
    ∃ (K : Subfield ℂ), NumberField K ∧
      ∃ pK : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p := by
  let x := p (IsLocalRing.closedPoint ℂ)
  let r : X.residueField x ⟶ CommRingCat.of ℂ :=
    X.descResidueField (Scheme.stalkClosedPointTo p)
  have : NumberField (X.residueField x) := residueField_numberField_of_closed f x hp
  let K := r.hom.fieldRange
  let e := r.hom.rangeRestrictFieldEquiv
  have hK : NumberField K := NumberField.of_ringEquiv (X.residueField x) K e
  refine ⟨K, hK, Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    X.fromSpecResidueField x, ?_⟩
  have heq : (CommRingCat.ofHom e.toRingHom) ≫
      (CommRingCat.ofHom K.subtype) = r := by
    apply CommRingCat.hom_ext
    ext z
    rfl
  rw [← Spec.map_comp_assoc, heq]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField ℂ X p

/-- In a locally finite-type rational scheme, an isolated complex point
has a model over a number field. -/
theorem complex_point_descends_of_isolated
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (hp : IsOpen {p (IsLocalRing.closedPoint ℂ)}) :
    ∃ (K : Subfield ℂ), NumberField K ∧
      ∃ pK : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  exact complex_point_descends_of_closed f p
    (isClosed_singleton_of_isLocallyClosed_singleton hp.isLocallyClosed)

/-- Isolation after a field extension is sufficient: projection from a
base change over a field is open, so the original point is also isolated. -/
theorem complex_point_descends_of_isolated_baseChange
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f]
    (p : Spec (CommRingCat.of ℂ) ⟶
      CategoryTheory.Limits.pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
    (hp : IsOpen {p (IsLocalRing.closedPoint ℂ)}) :
    ∃ (K : Subfield ℂ), NumberField K ∧
      ∃ pK : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom K.subtype) ≫ pK =
          p ≫ CategoryTheory.Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) := by
  let π := CategoryTheory.Limits.pullback.fst f
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))
  apply complex_point_descends_of_isolated f (p ≫ π)
  change IsOpen {π (p (IsLocalRing.closedPoint ℂ))}
  simpa only [Set.image_singleton] using
    π.isOpenMap {p (IsLocalRing.closedPoint ℂ)} hp

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints.Abelian
