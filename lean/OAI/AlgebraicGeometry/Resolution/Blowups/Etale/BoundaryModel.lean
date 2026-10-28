import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Monomial

/-! # Boundary Model -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel.Construction

noncomputable section

/-! Explicit étale normal-crossing models for individually labelled boundary equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

/-- Each labelled equation is an invertible factor times a distinct
coordinate, or is itself invertible. The actual étale map retains the
original ground algebra. -/
structure EtaleBoundaryModel (k A : Type u) (ι : Type v) [CommRing k] [CommRing A]
    [Algebra k A] (w : ι → A) where
  indices : Type u
  finite : Fintype indices
  decidableEq : DecidableEq indices
  map : MvPolynomial indices k →+* A
  etale : map.Etale
  ground : ∀ c : k, map (MvPolynomial.C c) = algebraMap k A c
  coordinate : ι → Option indices
  distinct : ∀ i j s, coordinate i = some s → coordinate j = some s → i = j
  multiplier : ι → A
  multiplierUnit : ∀ j, IsUnit (multiplier j)
  equation : ∀ j, w j = multiplier j *
    match coordinate j with
    | none => 1
    | some s => map (MvPolynomial.X s)

attribute [instance] EtaleBoundaryModel.finite EtaleBoundaryModel.decidableEq

/-- A normal-crossing model on an actual affine open through a specified
point, with all equations pulled back by the displayed algebra map. -/
structure EtaleBoundaryOpenChart (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} (w : ι → R)
    (p : PrimeSpectrum R) where
  carrier : CommRingCat.{u}
  algebra : Algebra k carrier
  map : R →ₐ[k] carrier
  isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom map.toRingHom))
  point : PrimeSpectrum carrier
  point_over : PrimeSpectrum.comap map.toRingHom point = p
  model : EtaleBoundaryModel k carrier ι (fun j => map (w j))

attribute [instance] EtaleBoundaryOpenChart.algebra EtaleBoundaryOpenChart.isOpenImmersion

variable {k A : Type u} {ι : Type v} [CommRing k] [CommRing A] [Algebra k A]
  {w : ι → A} (M : EtaleBoundaryModel k A ι w)

theorem EtaleBoundaryModel.component_ideal (j : ι) :
    Ideal.span {w j} = match M.coordinate j with
      | none => ⊤
      | some s => Ideal.span {M.map (MvPolynomial.X s)} := by
  rw [M.equation j]
  cases h : M.coordinate j with
  | none =>
      dsimp only
      rw [mul_one, Ideal.span_singleton_eq_top]
      exact M.multiplierUnit j
  | some s =>
      dsimp only
      exact Ideal.span_singleton_mul_left_unit (M.multiplierUnit j) _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel.Construction
