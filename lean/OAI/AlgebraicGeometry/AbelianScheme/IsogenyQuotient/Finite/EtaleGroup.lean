import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Descent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Etale
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Dimension
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELAction

/-! # Etale Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.EtaleGroup.Construction

noncomputable section

/-! FiniteDescent constructs the quotient by an actual finite etale closed group,
with its original dimension, literal kernel, and complementary map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

set_option backward.isDefEq.respectTransparency false in
theorem finiteEtaleGroupQuotient_exists {S : Scheme.{u}} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
    (H : Over S) [GrpObj H] [IsFinite H.hom] [Etale H.hom]
    (i : H ⟶ A.scheme) [IsMonHom i] (hi : IsClosedImmersion i.left)
    (n : ℕ) (hn : i ^ n = 1) :
    ∃ (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : B.scheme ⟶ A.scheme),
      Etale f.hom.left ∧ IsMonHom g ∧
      f.hom ≫ g = (𝟙 A.scheme) ^ n ∧ g ≫ f.hom = (𝟙 B.scheme) ^ n ∧
      (∀ (T : Over S) (a : T ⟶ A.scheme), a ≫ f.hom = 1 ↔ ∃! x : T ⟶ H, x ≫ i = a) ∧
      Descent.Construction.QuotientUniversalProperty i f.hom := by
  have : IsClosedImmersion i.left := hi
  have : Mono i := Over.mono_of_mono_left i
  obtain ⟨B0, f0, hfmon, hfin, hsurj, hker, hUP⟩ :=
    @Descent.Construction.verifiedFiniteDescentInput S (PELAction.Construction.abelianSchemeForgetDimension A) H inferInstance i inferInstance hi
      ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsMonHom f0 := hfmon
  have : IsFinite f0.left := hfin.1
  have : Flat f0.left := hfin.2.1
  have : LocallyOfFinitePresentation f0.left := hfin.2.2
  have : Surjective f0.left := hsurj
  have he : Etale f0.left := IsogenyQuotient.Etale.Construction.quotient_etale_of_etale_kernel i f0 hker
  have hif : i ≫ f0 = 1 := (hker H i).mpr
    ⟨𝟙 _, Category.id_comp _, fun x hx => (cancel_mono i).mp (hx.trans (Category.id_comp i).symm)⟩
  obtain ⟨g, ⟨hfg, hgf⟩, _⟩ := Descent.Construction.complementary_map_of_FiniteDescent i f0 hif hUP n hn
  have : EffectiveEpi (f0 ⊗ₘ f0) := Picard.PoincareBundle.Epi.Construction.effectiveEpi_tensor_over_of_fpqc f0 f0
  have : IsMonHom ((𝟙 A.scheme) ^ n) := Picard.PoincareBundle.Epi.Construction.isMonHom_pow (𝟙 A.scheme) n
  have hg : IsMonHom g := Picard.PoincareBundle.Epi.Construction.isMonHom_of_comp f0 _ g hfg
  let B := Dimension.Construction.abelianQuotientWithDimension A B0 f0
  let f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B := {
    hom := f0, preservesGroup := hfmon, finite := hfin.1, flat := hfin.2.1, surjective := hsurj }
  exact ⟨B, f, g, he, hg, hfg, hgf, hker, hUP⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.EtaleGroup.Construction
