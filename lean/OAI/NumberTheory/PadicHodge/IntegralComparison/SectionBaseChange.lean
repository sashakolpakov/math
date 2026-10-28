import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms

/-! # Section Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionBaseChange

noncomputable section

/-!
# IntegralComparison: the original section-ring coefficient maps commute with arbitrary change of base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (ρ : R →+* S) (X : Over (Spec (CommRingCat.of S)))

def restrictBase : Over (Spec (CommRingCat.of R)) :=
  (Over.map (Spec.map (CommRingCat.ofHom ρ))).obj X

theorem sectionBase_comp (U : X.left.Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (restrictBase ρ X).hom.appLE ⊤ U le_top =
      CommRingCat.ofHom ρ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ X.hom.appLE ⊤ U le_top := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (X.hom ≫ Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ U _ = _
  rw [← Scheme.Hom.appLE_comp_appLE X.hom (Spec.map (CommRingCat.ofHom ρ)) ⊤ ⊤ U le_top le_top]
  have htop : (Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom ρ)).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  rw [htop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem sectionBaseMap_comp (U : X.left.Opens) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R (restrictBase ρ X) U =
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap S X U).comp ρ :=
  congrArg (fun f : CommRingCat.of R ⟶ Γ(X.left, U) => f.hom) (sectionBase_comp ρ X U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionBaseChange
