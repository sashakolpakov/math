import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveComparison

/-! # Projective Quasi Iso Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A map from a K-projective complex lifts through a quasi-isomorphism
up to an actual cochain homotopy. This supplies comparisons between finite
projective models without choosing a retraction from a Cech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.HomologicalComplex DerivedCategory

universe u v

open _root_.CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] HasDerivedCategory.standard in
theorem ProjectiveBasic.CochainComplex.IsKProjective.exists_lift_through_quasiIso
    {K L M : CochainComplex C ℤ} [ProjectiveBasic.CochainComplex.IsKProjective K]
    (p : L ⟶ M) [QuasiIso p] (f : K ⟶ M) :
    ∃ g : K ⟶ L, Nonempty (Homotopy (g ≫ p) f) := by
  obtain ⟨a, ha⟩ := (ProjectiveBasic.CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient _ _).obj L)).surjective
    ((quotientCompQhIso C).hom.app K ≫ Q.map f ≫ inv (Q.map p) ≫
      (quotientCompQhIso C).inv.app L)
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective a
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (ProjectiveBasic.CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient _ _).obj M)).injective
  simp only [Functor.map_comp, hg, ha]
  simp only [Category.assoc, ← quotientCompQhIso_inv_naturality p,
    IsIso.inv_hom_id_assoc]
  rw [quotientCompQhIso_inv_naturality f, Iso.hom_inv_id_app_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
