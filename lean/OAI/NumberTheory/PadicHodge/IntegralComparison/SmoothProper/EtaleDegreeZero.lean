import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConnectedComponents
import OAI.NumberTheory.PadicHodge.IntegralComparison.Interfaces

/-! # Etale Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleDegreeZero

noncomputable section

/-! An unconditional integral Frobenius polynomial for the original geometric étale cohomology in degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

section Geometry

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [QuasiCompact f]

instance geometric_noetherian : IsNoetherian (Frobenius.Geometry.geometricFiber (L := L) f) := by
  let g : Frobenius.Geometry.geometricFiber (L := L) f ⟶ Spec (CommRingCat.of L) :=
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  let : IsLocallyNoetherian (Frobenius.Geometry.geometricFiber (L := L) f) :=
    LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace (Frobenius.Geometry.geometricFiber (L := L) f) :=
    QuasiCompact.compactSpace_of_compactSpace g
  exact {}

end Geometry

variable (p a : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [Fintype k] [CharP k p]
variable (hcard : Fintype.card k = p ^ a)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

def permutation : Equiv.Perm (_root_.ConnectedComponents (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) f)) :=
  Etale.ConnectedComponents.permutation _
    (Frobenius.Geometry.geometricFiberIso f (Frobenius.Geometry.geometricFrobenius p a k hcard))

def polynomial : Polynomial ℤ :=
  Etale.ConnectedComponents.polynomial _
    (Frobenius.Geometry.geometricFiberIso f (Frobenius.Geometry.geometricFrobenius p a k hcard))

theorem polynomial_monic : (polynomial p a k hcard f).Monic :=
  Etale.ConnectedComponents.polynomial_monic _ _

variable (ℓ : ℕ) [Fact ℓ.Prime]

omit p a [Fact p.Prime] [Fintype k] [CharP k p] hcard in
instance finite : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f 0) :=
  PeriodInvariants.EtaleDegreeZero.degreeZero_finite ℓ _

theorem charpoly :
    (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f 0).charpoly =
      (polynomial p a k hcard f).map (Int.castRingHom ℚ_[ℓ]) :=
  Etale.ConnectedComponents.charpoly ℓ _ _

omit p a [Fact p.Prime] [Fintype k] [CharP k p] hcard in
theorem finrank : Module.finrank ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f 0) =
    Nat.card (_root_.ConnectedComponents (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) f)) :=
  Etale.ConnectedComponents.finrank ℓ _

theorem trace_pow (n : ℕ) :
    LinearMap.trace ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f 0)
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f 0 ^ n) =
      (Nat.card {c // (permutation p a k hcard f ^ n) c = c} : ℚ_[ℓ]) := by
  classical
  let : Fintype (_root_.ConnectedComponents (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) f)) :=
    Fintype.ofFinite _
  exact (Etale.ConnectedComponents.trace_pow ℓ _
    (Frobenius.Geometry.geometricFiberIso f (Frobenius.Geometry.geometricFrobenius p a k hcard)) n).trans
      (by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl)

theorem exists_monic :
    ∃ hfin : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f 0),
      letI := hfin
      ∃ P : Polynomial ℤ, P.Monic ∧
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f 0).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ]) :=
  ⟨finite k f ℓ, polynomial p a k hcard f, polynomial_monic p a k hcard f,
    EtaleDegreeZero.charpoly p a k hcard f ℓ⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleDegreeZero
