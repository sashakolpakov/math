import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover

/-! # Open Sheaf Of -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf.OpenSheafSections

noncomputable section

/-! Sections on an open chart are the actual sections on its image, naturally for sheaf morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (W : X.Opens) (hW : f ''ᵁ ⊤ = W)

def iso (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f).obj F).obj.obj (op ⊤) ≅ F.obj.obj (op W) :=
  F.obj.mapIso (eqToIso (congrArg op hW))

theorem naturality {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (φ : F ⟶ G) :
    (iso R f W hW F).hom ≫ φ.hom.app (op W) =
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f).map φ).hom.app (op ⊤) ≫ (iso R f W hW G).hom :=
  φ.hom.naturality (eqToHom (congrArg op hW))

include hW in
theorem epi_of_chart {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (φ : F ⟶ G)
    (hφ : Epi (((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f).map φ).hom.app (op ⊤))) :
    Epi (φ.hom.app (op W)) := by
  have : IsIso (iso R f W hW G).hom := (iso R f W hW G).isIso_hom
  have : Epi (((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f).map φ).hom.app (op ⊤) ≫
      (iso R f W hW G).hom) := inferInstance
  have : Epi ((iso R f W hW F).hom ≫ φ.hom.app (op W)) :=
    (OpenSheafSections.naturality R f W hW φ).symm ▸ this
  exact epi_of_epi (iso R f W hW F).hom (φ.hom.app (op W))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf.OpenSheafSections
