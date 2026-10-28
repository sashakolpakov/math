import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.BoundaryCenterReplacement
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Adapted Center Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterChart.Construction

noncomputable section

/-! Actual affine open charts whose center frame contains every prescribed boundary equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Insert the new boundary at index zero and retain all old boundary
indices in the complementary center frame. -/
def insertRetainedCenterIndex {α : Type u} {n : ℕ}
    (e : Fin n ↪ α) (i : α) (hi : ∀ j, i ≠ e j) :
    Fin (n + 1) ↪ Option {j : α // i ≠ j} :=
  (finSuccEquiv n).toEmbedding.trans
    (Function.Embedding.optionMap
      ⟨(fun j => ⟨e j, hi j⟩), fun _ _ h => e.injective (congrArg Subtype.val h)⟩)

theorem insertRetainedCenterIndex_zero {α : Type u} {n : ℕ}
    (e : Fin n ↪ α) (i : α) (hi : ∀ j, i ≠ e j) : insertRetainedCenterIndex e i hi 0 = none := rfl

theorem insertRetainedCenterIndex_succ {α : Type u} {n : ℕ}
    (e : Fin n ↪ α) (i : α) (hi : ∀ j, i ≠ e j) (j : Fin n) :
    insertRetainedCenterIndex e i hi j.succ = some ⟨e j, hi j⟩ := by
  change Option.map (fun j => (⟨e j, hi j⟩ : {j : α // i ≠ j})) ((finSuccEquiv n) j.succ) = _
  rw [finSuccEquiv_succ]
  rfl

/-- The actual point over the source prime and the exact center ideal
are retained along with a dual frame and an injective indexing of all
prescribed boundary equations among the center generators. -/
structure BoundaryAdaptedCenterOpenChart (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] (I : Ideal R) {n : ℕ} (w : Fin n → R)
    (p : PrimeSpectrum R) where
  carrier : CommRingCat.{u}
  algebra : Algebra k carrier
  map : R →ₐ[k] carrier
  isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom map.toRingHom))
  point : PrimeSpectrum carrier
  point_over : PrimeSpectrum.comap map.toRingHom point = p
  indices : Type u
  finite : Fintype indices
  decidableEq : DecidableEq indices
  generators : indices → carrier
  derivations : indices → Derivation k carrier carrier
  dual : ∀ i j, derivations i (generators j) = if i = j then 1 else 0
  centerSpan : Ideal.span (Set.range generators) = I.map map.toRingHom
  boundaryIndex : Fin n ↪ indices
  boundaryCoordinates : ∀ i, generators (boundaryIndex i) = map (w i)

attribute [instance] BoundaryAdaptedCenterOpenChart.algebra BoundaryAdaptedCenterOpenChart.isOpenImmersion
  BoundaryAdaptedCenterOpenChart.finite BoundaryAdaptedCenterOpenChart.decidableEq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AdaptedCenterChart.Construction
