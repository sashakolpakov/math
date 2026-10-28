import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FramedTate
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.SplitScalar
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateKernels
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateGeometry

/-! # Tate Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateLattices.Construction

noncomputable section

/-! Full intrinsic Tate preimages are reconstructed from the projected
chosen and opposite lattices of actual PEL isogenies. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {R : Type} [CommRing R] {g N s n m q : ℕ} [Fact q.Prime]
  {P Q Q' : TateComparison.PEL.PELFamilyData R g N S} (T : Over S)

def framedTatePreimage (e : TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q) (f : TateComparison.PELIsogenies.PELIsogeny P Q n) :
    Submodule ℤ_[q] (TateComparison.Rational.SplitTateSpace s q) :=
  (TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) f.isogeny.hom).map
    (e.toLinearMap.restrictScalars ℤ_[q])

theorem framedTatePreimage_eq_comap
    (e : TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q)
    (e' : TateComparison.Rational.SplitTateFrame s Q.abelian.scheme T q) (f : TateComparison.PELIsogenies.PELIsogeny P Q n) :
    framedTatePreimage T e f = (TateComparison.Rational.framedIntegralTateImage e').comap
      ((FramedTate.Construction.framedRationalTateMap T q e e' f).restrictScalars ℤ_[q]) := by
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e' (TateComparison.Rational.rationalTateMap (T := T) (q := q) f.isogeny.hom (e.symm (e x))) ∈
      (TateComparison.Rational.integralTateImage Q.abelian.scheme T q).map (e'.toLinearMap.restrictScalars ℤ_[q])
    rw [e.symm_apply_apply]
    exact Submodule.mem_map_of_mem hx
  · intro hz
    change e' (TateComparison.Rational.rationalTateMap (T := T) (q := q) f.isogeny.hom (e.symm z)) ∈
      (TateComparison.Rational.integralTateImage Q.abelian.scheme T q).map (e'.toLinearMap.restrictScalars ℤ_[q]) at hz
    obtain ⟨x, hx, he⟩ := hz
    change e' x = e' (TateComparison.Rational.rationalTateMap (T := T) (q := q) f.isogeny.hom (e.symm z)) at he
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    change TateComparison.Rational.rationalTateMap (T := T) (q := q) f.isogeny.hom (e.symm z) ∈ TateComparison.Rational.integralTateImage _ T q
    rw [← e'.injective he]
    exact hx

theorem framedTatePreimage_split
    (χ : Fin s × Bool → R →+* ℤ_[q])
    (hsep : ∀ i j : Fin s × Bool, i ≠ j → ∃ b : R, (χ i b : ℚ_[q]) ≠ (χ j b : ℚ_[q]))
    (e : TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q)
    (e' : TateComparison.Rational.SplitTateFrame s Q.abelian.scheme T q)
    (he : TateComparison.Rational.IsSplitActionFrame P T q χ e) (he' : TateComparison.Rational.IsSplitActionFrame Q T q χ e')
    (L : Fin s × Bool → Submodule ℤ_[q] (Fin 3 → ℚ_[q]))
    (hL : TateComparison.Rational.framedIntegralTateImage e' = Submodule.pi Set.univ L)
    (f : TateComparison.PELIsogenies.PELIsogeny P Q n) :
    ∀ z ∈ framedTatePreimage T e f, ∀ i, Pi.single i (z i) ∈ framedTatePreimage T e f := by
  intro z hz i
  rw [framedTatePreimage_eq_comap T e e' f, hL] at hz ⊢
  change FramedTate.Construction.framedRationalTateMap T q e e' f z ∈ Submodule.pi Set.univ L at hz
  change FramedTate.Construction.framedRationalTateMap T q e e' f (Pi.single i (z i)) ∈ Submodule.pi Set.univ L
  rw [Submodule.mem_pi] at hz ⊢
  intro j _
  by_cases hji : j = i
  · subst j
    rw [← SplitScalar.Construction.intertwiner_coordinate (fun b v => (χ v b : ℚ_[q])) hsep
      (FramedTate.Construction.framedRationalTateMap T q e e' f)
      (FramedTate.Construction.framedRationalTateMap_intertwines T q χ e e' he he' f)]
    exact hz i (Set.mem_univ _)
  · rw [SplitScalar.Construction.intertwiner_single_off_diagonal (fun b v => (χ v b : ℚ_[q])) hsep
      (FramedTate.Construction.framedRationalTateMap T q e e' f)
      (FramedTate.Construction.framedRationalTateMap_intertwines T q χ e e' he he' f) i j (Ne.symm hji)]
    exact (L j).zero_mem

/-- Equality of the TateComparison chosen and opposite projections implies equality
of the full intrinsic isogeny preimage lattice. -/
theorem intrinsic_preimage_eq_of_framed_lattices
    (χ : Fin s × Bool → R →+* ℤ_[q])
    (hsep : ∀ i j : Fin s × Bool, i ≠ j → ∃ b : R, (χ i b : ℚ_[q]) ≠ (χ j b : ℚ_[q]))
    (e : TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q)
    (eQ : TateComparison.Rational.SplitTateFrame s Q.abelian.scheme T q)
    (eQ' : TateComparison.Rational.SplitTateFrame s Q'.abelian.scheme T q)
    (he : TateComparison.Rational.IsSplitActionFrame P T q χ e)
    (heQ : TateComparison.Rational.IsSplitActionFrame Q T q χ eQ) (heQ' : TateComparison.Rational.IsSplitActionFrame Q' T q χ eQ')
    (L L' : Fin s × Bool → Submodule ℤ_[q] (Fin 3 → ℚ_[q]))
    (hL : TateComparison.Rational.framedIntegralTateImage eQ = Submodule.pi Set.univ L)
    (hL' : TateComparison.Rational.framedIntegralTateImage eQ' = Submodule.pi Set.univ L')
    (f : TateComparison.PELIsogenies.PELIsogeny P Q n) (f' : TateComparison.PELIsogenies.PELIsogeny P Q' m)
    (hlat : ∀ i : Fin s × Bool, TateComparison.Rational.framedTateLattice e f.isogeny.hom i =
      TateComparison.Rational.framedTateLattice e f'.isogeny.hom i) :
    TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) f.isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) f'.isogeny.hom := by
  apply Submodule.map_injective_of_injective (f := e.toLinearMap.restrictScalars ℤ_[q]) e.injective
  exact SplitScalar.Construction.split_submodule_eq_of_projections (framedTatePreimage T e f) (framedTatePreimage T e f')
    (framedTatePreimage_split T χ hsep e eQ he heQ L hL f)
    (framedTatePreimage_split T χ hsep e eQ' he heQ' L' hL' f') hlat

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateLattices.Construction
