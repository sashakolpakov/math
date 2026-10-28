import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

/-! # PEL Polarization Class -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual isogeny polarization and Poincare equations give the
similitude identity for the original polarization biextension class.
This holds on the family itself, before taking periods or Tate modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}

def PEL.PELFamilyData.polarizationClass (P : PEL.PELFamilyData R g N S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (P.abelian.scheme ⊗ P.abelian.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (P.polarizationMap.hom ⊗ₘ 𝟙 P.abelian.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare)

variable {P Q : PEL.PELFamilyData R g N S} {n : ℕ} (e : PELIsogenies.PELIsogeny P Q n)

theorem PELIsogenies.PELIsogeny.polarizationClass_similitude :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.isogeny.hom ⊗ₘ e.isogeny.hom).left Q.polarizationClass =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (((𝟙 P.abelian.scheme) ^ n) ⊗ₘ 𝟙 P.abelian.scheme).left
        P.polarizationClass := by
  let u := (e.isogeny.hom ≫ Q.polarizationMap.hom) ⊗ₘ 𝟙 P.abelian.scheme
  have hp := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass u.left) e.poincare
  have hleft : u ≫ (𝟙 Q.dual.abelian.scheme ⊗ₘ e.isogeny.hom) =
      (e.isogeny.hom ⊗ₘ e.isogeny.hom) ≫ (Q.polarizationMap.hom ⊗ₘ 𝟙 Q.abelian.scheme) := by
    simp only [u, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  have hright : u ≫ (e.dualHom ⊗ₘ 𝟙 P.abelian.scheme) =
      (((𝟙 P.abelian.scheme) ^ n) ⊗ₘ 𝟙 P.abelian.scheme) ≫
        (P.polarizationMap.hom ⊗ₘ 𝟙 P.abelian.scheme) := by
    simp only [u, tensorHom_comp_tensorHom, Category.id_comp, Category.assoc,
      e.polarization, MonObj.pow_comp]
  simp only [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left] at hp
  rw [hleft, hright] at hp
  simpa only [Over.comp_left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, PEL.PELFamilyData.polarizationClass] using hp

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
