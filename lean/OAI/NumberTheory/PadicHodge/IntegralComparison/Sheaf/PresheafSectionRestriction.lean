import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.EquivalentPresheafSections

/-! # Presheaf Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction

noncomputable section

/-! Actual presheaf sections of sheaf complexes restrict by precomposition along the geometric site functor. -/

open _root_.CategoryTheory

universe u v z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  [HasExt.{max u z} (Sheaf K (ModuleCat.{u} R))]

instance restriction_additive : (F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).Additive where
  map_add := rfl

def map : PresheafSectionComplex.sectionFunctor.{u, v, u, z} R K ⟶
    F.sheafPushforwardContinuous (ModuleCat.{u} R) J K ⋙
      PresheafSectionComplex.sectionFunctor.{u, v, u, z} R J where
  app M := (ModuleCat.uliftFunctor.{z, u} R).map
    (ModuleCat.ofHom (EquivalentPresheafSections.map R F (ModuleCat.of R R) M.obj))
  naturality _ _ φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def complexMap (L : CochainComplex (Sheaf K (ModuleCat.{u} R)) ℕ) :
    PresheafSectionComplex.complex.{u, v, u, z} R K L ⟶
      PresheafSectionComplex.complex.{u, v, u, z} R J
        (((F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).mapHomologicalComplex (.up ℕ)).obj L) :=
  (NatTrans.mapHomologicalComplex (PresheafSectionRestriction.map F R J K) (.up ℕ)).app L

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction
