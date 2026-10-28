import OAI.AlgebraicGeometry.Picard.PoincareBundle.SectionNormalizedTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Normalized Kernel Translation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation

noncomputable section

/-! Normalize subgroup translation along the actual identity section of the subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [GrpObj A]
  (i : H ⟶ A) [IsMonHom i]

/-- The subgroup translation map on the actual product. -/
def action : H ⊗ A ⟶ A := (i ⊗ₘ 𝟙 A) ≫ μ[A]

/-- Insert the subgroup identity and leave the starting point unchanged. -/
def sectionMap : A ⟶ H ⊗ A := lift (1 : A ⟶ H) (𝟙 A)

omit [GrpObj A] in
theorem section_source : sectionMap (H := H) (A := A) ≫ snd H A = 𝟙 A := lift_snd _ _

theorem section_action : sectionMap (H := H) (A := A) ≫ action i = 𝟙 A := by
  change lift (1 : A ⟶ H) (𝟙 A) ≫ (i ⊗ₘ 𝟙 A) ≫ μ[A] = 𝟙 A
  rw [← Category.assoc, lift_map, MonObj.one_comp, Category.id_comp]
  change (1 : A ⟶ A) * (𝟙 A) = 𝟙 A
  exact one_mul _

variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

/-- Restricting the translated line at the subgroup identity recovers the original line. -/
def targetIso :
    (Scheme.Modules.pullback (sectionMap (H := H) (A := A)).left).obj (L.pullback (action i).left).sheaf ≅
      L.sheaf :=
  (Scheme.Modules.pullbackComp (sectionMap (H := H) (A := A)).left (action i).left ≪≫
    Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (section_action i)) ≪≫
      Scheme.Modules.pullbackId A.left).app L.sheaf

variable (t : (L.pullback (snd H A).left).sheaf ≅ (L.pullback (action i).left).sheaf)

/-- Correct any actual translation isomorphism to agree with the identity at the subgroup unit. -/
def normalized : (L.pullback (snd H A).left).sheaf ≅ (L.pullback (action i).left).sheaf :=
  SectionNormalizedTransport.normalized (snd H A).left (sectionMap (H := H) (A := A)).left
    (congrArg Over.Hom.left (section_source (H := H) (A := A))) L.sheaf
      (L.pullback (action i).left).sheaf t (targetIso i L)

theorem normalized_unit :
    (Scheme.Modules.pullback (sectionMap (H := H) (A := A)).left).map (normalized i L t).hom ≫
        (targetIso i L).hom =
      (SectionNormalizedTransport.sourceIso (snd H A).left
        (sectionMap (H := H) (A := A)).left
        (congrArg Over.Hom.left (section_source (H := H) (A := A))) L.sheaf).hom :=
  SectionNormalizedTransport.normalized_section (snd H A).left
    (sectionMap (H := H) (A := A)).left
    (congrArg Over.Hom.left (section_source (H := H) (A := A))) L.sheaf
      (L.pullback (action i).left).sheaf t (targetIso i L)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation
