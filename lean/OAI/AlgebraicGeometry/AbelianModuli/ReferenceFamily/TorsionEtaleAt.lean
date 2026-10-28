import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupSplittingAt
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Finiteness
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Torsion Etale At -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt.TorsionEtale

noncomputable section

/-! Finite etaleness and local finite-group splittings for HilbertConstruction's actual
torsion kernel over every characteristic-zero base. TorsionQuotient's committed proof
is applied to the multiplication morphism itself. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem torsion_finite_etale_of_stalk_units
    (hN : ∀ x : S, IsUnit (N : S.presheaf.stalk x)) :
    IsFinite (A.torsionScheme N).hom ∧ Etale (A.torsionScheme N).hom := by
  let : Etale (A.multiplication N).left :=
    AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale A.scheme N hN
  have he : Etale (A.torsionScheme N).hom :=
    inferInstanceAs (Etale (Limits.pullback.snd (A.multiplication N).left η[A.scheme].left))
  let : Etale (A.torsionScheme N).hom := he
  exact ⟨AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified _, he⟩

theorem integer_unit_at_stalk {K : Type} [Field K] [CharZero K]
    (p : S ⟶ Spec (.of K)) (N : ℕ) [NeZero N] (x : S) :
    IsUnit (N : S.presheaf.stalk x) := by
  let constants : K →+* Γ(S, ⊤) := p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let toStalk : K →+* S.presheaf.stalk x :=
    (S.presheaf.germ ⊤ x (by trivial)).hom.comp constants
  have hu : IsUnit (N : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  simpa only [map_natCast] using hu.map toStalk

theorem torsion_finite_etale {K : Type} [Field K] [CharZero K]
    (p : S ⟶ Spec (.of K)) (N : ℕ) [NeZero N] :
    IsFinite (A.torsionScheme N).hom ∧ Etale (A.torsionScheme N).hom :=
  torsion_finite_etale_of_stalk_units A (integer_unit_at_stalk p N)

/-- The actual finite-etale frame scheme now needs no marking or
finite-etaleness assumption on a characteristic-zero base. -/
theorem frame_finite_etale {K : Type} [Field K] [CharZero K]
    (p : S ⟶ Spec (.of K)) (N : ℕ) [NeZero N] :
    IsFinite (Level.Cover.LevelCover.frameScheme A N).hom ∧ Etale (Level.Cover.LevelCover.frameScheme A N).hom := by
  obtain ⟨hf, he⟩ := torsion_finite_etale A p N
  let : IsFinite (A.torsionScheme N).hom := hf
  let : Etale (A.torsionScheme N).hom := he
  exact Frame.Finiteness.LevelCover.frameScheme_finite_etale A

/-- Every point has an etale neighborhood with a constructed finite
constant torsion group. No full-level structure is assumed. -/
theorem exists_torsion_group_splitting_at {K : Type} [Field K] [CharZero K]
    (p : S ⟶ Spec (.of K)) (N : ℕ) [NeZero N] (s : S) :
    ∃ (T : Scheme.{0}) (u : T ⟶ S), Etale u ∧ s ∈ Set.range u ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G), Nonempty
        (HilbertConstruction.Constant.GroupMaps.constantGroupFunctor T G ≅ (Over.map u).op ⋙ A.torsionFunctor N) := by
  obtain ⟨hf, he⟩ := torsion_finite_etale A p N
  let : IsFinite (A.torsionScheme N).hom := hf
  let : Etale (A.torsionScheme N).hom := he
  exact GroupSplittingAt.GroupSplitting.exists_torsion_group_splitting_at A s

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt.TorsionEtale
