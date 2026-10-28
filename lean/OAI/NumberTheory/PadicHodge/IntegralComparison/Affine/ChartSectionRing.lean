import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

/-! # Chart Section Ring -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSectionRing

noncomputable section

/-!
# IntegralComparison: the actual coordinate ring of an affine chart identifies with sections on its Zariski image
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k C : Type u) [CommRing k] [CommRing C]
  (X : Over (Spec (CommRingCat.of k))) (g : Spec (CommRingCat.of C) ⟶ X.left) [IsOpenImmersion g]

theorem top_le_preimage : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ g ⁻¹ᵁ g.opensRange := by
  rw [Scheme.Hom.preimage_opensRange]

def sectionMap : Γ(X.left, g.opensRange) ⟶ CommRingCat.of C :=
  g.appLE g.opensRange ⊤ (top_le_preimage k C X g) ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom

private def imageIso : Γ(X.left, g.opensRange) ≅ Γ(Spec (CommRingCat.of C), ⊤) := by
  letI : IsIso (g.app g.opensRange) := Scheme.Hom.isIso_app g g.opensRange le_rfl
  exact asIso (g.app g.opensRange) ≪≫
    (Spec (CommRingCat.of C)).presheaf.mapIso (eqToIso (Scheme.Hom.preimage_opensRange g).symm).op

private theorem imageIso_hom : (imageIso k C X g).hom = g.appLE g.opensRange ⊤ (top_le_preimage k C X g) := by
  apply congrArg (fun a => g.app g.opensRange ≫ a)
  apply congrArg (Spec (CommRingCat.of C)).presheaf.map
  exact Subsingleton.elim _ _

def iso : Γ(X.left, g.opensRange) ≅ CommRingCat.of C := imageIso k C X g ≪≫ Scheme.ΓSpecIso (CommRingCat.of C)

theorem iso_hom : (iso k C X g).hom = sectionMap k C X g :=
  congrArg (fun a => a ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) (imageIso_hom k C X g)

variable [Algebra k C] (hg : g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k C)))

include hg in
theorem base_square : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    X.hom.appLE ⊤ g.opensRange le_top ≫ sectionMap k C X g = CommRingCat.ofHom (algebraMap k C) := by
  have h₁ := Scheme.Hom.appLE_comp_appLE g X.hom ⊤ g.opensRange ⊤ le_top (top_le_preimage k C X g)
  have h₂ := congrArg (fun a : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of k) => a.appLE ⊤ ⊤ le_top) hg
  have h₃ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k C))
  calc
    _ = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X.hom.appLE ⊤ g.opensRange le_top ≫ g.appLE g.opensRange ⊤ (top_le_preimage k C X g)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of C)).hom := (Category.assoc _ _ _).symm
    _ = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k C))).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom :=
      congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ a ≫
        (Scheme.ΓSpecIso (CommRingCat.of C)).hom) (h₁.trans h₂)
    _ = CommRingCat.ofHom (algebraMap k C) := by rw [h₃, Iso.inv_hom_id_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSectionRing
