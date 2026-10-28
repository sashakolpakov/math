import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplication
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BaseChangePoints

/-! # Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Polarization.Construction

noncomputable section

/-!
Relative polarization homomorphisms from field-level PoincareBundle maps, with all
multiplication hypotheses discharged. TorsionQuotient is used in its complete repaired
form. No fpqc, surjectivity, or finite-type property of [n] is an input.
The remaining field input is the actual PoincareBundle morphism and pullback identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- Construct the relative homomorphism from PoincareBundle on geometric fibers.
This derives the formerly explicit [n]-map hypotheses from TorsionQuotient. -/
theorem relative_polarization_from_field_morphisms
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
        IsMonHom p ∧
        (Over.pullback s).map f.hom ≫ p ≫ (Over.pullback s).map fd =
          ((Over.pullback s).map polarization) ^ n) :
    ∃! p : B.toOver ⟶ BD.toOver,
      IsMonHom p ∧ f.hom ≫ p ≫ fd = polarization ^ n := by
  obtain ⟨_, hAnflat, hAnsurj, _, _⟩ := Multiplication.Construction.multiplication_geometry_from_TorsionQuotient A.toOver n
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.toOver) base n hn h_TorsionQuotient)
  have : Flat (((𝟙 A.toOver) ^ n).left) := hAnflat
  have : Surjective (((𝟙 A.toOver) ^ n).left) := hAnsurj
  have : QuasiCompact (((𝟙 A.toOver) ^ n).left) := by
    have : IsProper (((𝟙 A.toOver) ^ n).left) :=
      ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.multiplicationMap_isProper A.toOver n
    infer_instance
  have : EffectiveEpi ((𝟙 A.toOver) ^ n) := Picard.PoincareBundle.Epi.Construction.effectiveEpi_over_of_fpqc _
  obtain ⟨hBnfinite, hBnflat, hBnsurj, _, _⟩ := Multiplication.Construction.multiplication_geometry_from_TorsionQuotient B.toOver n
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := B.toOver) base n hn h_TorsionQuotient)
  have : IsFinite (((𝟙 B.toOver) ^ n).left) := hBnfinite
  have : Flat (((𝟙 B.toOver) ^ n).left) := hBnflat
  have : Surjective (((𝟙 B.toOver) ^ n).left) := hBnsurj
  have : EffectiveEpi f.hom := Picard.PoincareBundle.Epi.Construction.effectiveEpi_over_of_fpqc f.hom
  apply Polarization.Construction.relative_polarization_homomorphism n f.hom g fd gd polarization hfg hfdgd hgdfd
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := BD.toOver) base n hn h_TorsionQuotient).2
  intro L _ _ s
  obtain ⟨p, hp, hidentity⟩ := h_PoincareBundle L s
  have : IsMonHom p := hp
  exact ⟨BaseChangePoints.Construction.fieldMorphismOnPoints s p,
    BaseChangePoints.Construction.field_polarization_identity_on_points s n f.hom fd polarization p hidentity⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Polarization.Construction
