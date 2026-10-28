import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberHomEquality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Fiberwise

/-! # Polarization Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationIsogeny.Construction

noncomputable section

/-!
Construct the relative polarization isogeny from the geometric-field PoincareBundle
maps. The relative finiteness, flatness, and surjectivity are conclusions:
the field maps agree with the constructed relative map as scheme morphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- PoincareBundle's actual field isogenies yield a unique relative group map with
the polarization pullback identity, and this map is an isogeny. -/
theorem relative_polarization_isogeny_from_field_morphisms
    {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
    (base : S ⟶ Spec (.of K))
    (A B AD BD : Picard.PoincareBundle.Epi.Construction.AbelianScheme S)
    (n : ℕ) (hn : 0 < n)
    (f : Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny A B)
    (g : B.toOver ⟶ A.toOver) [IsMonHom g]
    (fd : BD.toOver ⟶ AD.toOver) [IsMonHom fd]
    (gd : AD.toOver ⟶ BD.toOver) [IsMonHom gd]
    (polarization : A.toOver ⟶ AD.toOver) [IsMonHom polarization]
    (hfg : f.hom ≫ g = (𝟙 A.toOver) ^ n)
    (hfdgd : fd ≫ gd = (𝟙 BD.toOver) ^ n)
    (hgdfd : gd ≫ fd = (𝟙 AD.toOver) ^ n)
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u})
    (h_PoincareBundle : ∀ (L : Type u) [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S),
      ∃ p : (Over.pullback s).obj B.toOver ⟶ (Over.pullback s).obj BD.toOver,
        IsMonHom p ∧ IsFinite p.left ∧ Flat p.left ∧ Surjective p.left ∧
        (Over.pullback s).map f.hom ≫ p ≫ (Over.pullback s).map fd =
          ((Over.pullback s).map polarization) ^ n) :
    ∃ p : Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny B BD,
      f.hom ≫ p.hom ≫ fd = polarization ^ n ∧
      (∀ r : B.toOver ⟶ BD.toOver, IsMonHom r →
        f.hom ≫ r ≫ fd = polarization ^ n → r = p.hom) ∧
      (∀ (L : Type u) [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S)
        (r : (Over.pullback s).obj B.toOver ⟶ (Over.pullback s).obj BD.toOver),
        IsMonHom r →
        (Over.pullback s).map f.hom ≫ r ≫ (Over.pullback s).map fd =
          ((Over.pullback s).map polarization) ^ n →
        (Over.pullback s).map p.hom = r) := by
  obtain ⟨p, ⟨hpmon, hp⟩, huniq⟩ := Relative.Polarization.Construction.relative_polarization_from_field_morphisms
    base A B AD BD n hn f g fd gd polarization hfg hfdgd hgdfd h_TorsionQuotient
    (fun L _ _ s => by
      obtain ⟨r, hrmon, _, _, _, hr⟩ := h_PoincareBundle L s
      exact ⟨r, hrmon, hr⟩)
  have : IsMonHom p := hpmon
  have hmatch := FiberHomEquality.Construction.relative_polarization_matches_field_morphism
    base A B AD BD n hn f fd gd polarization hfdgd p hp h_TorsionQuotient
  let pIso := Fiberwise.Construction.isogenyFromGeometricFibers B BD p (fun L _ _ s => by
    obtain ⟨r, hrmon, hrfin, hrflat, hrsurj, hr⟩ := h_PoincareBundle L s
    have : IsMonHom r := hrmon
    rw [hmatch L s r hr]
    exact ⟨hrfin, hrflat, hrsurj⟩)
  refine ⟨pIso, hp, ?_, ?_⟩
  · intro r hrmon hr
    exact huniq r ⟨hrmon, hr⟩
  · intro L _ _ s r hrmon hr
    have : IsMonHom r := hrmon
    exact hmatch L s r hr

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationIsogeny.Construction
