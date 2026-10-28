import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange

/-! # Top Restriction Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionBaseChange.CechTopRestrictionBaseChange

noncomputable section

/-! Base change preserves top-section restriction through the terminal-object comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v a b w
variable {C : Type u} [SemilatticeInf C] [OrderTop C]
  {D : Type v} [SemilatticeInf D] [OrderTop D]
  {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{w} A]
  (F : C ⥤ D) [PreservesFiniteLimits F] (e : F.obj ⊤ ≅ ⊤)
  {ι : Type w} (U : ι → C) (P : Dᵒᵖ ⥤ A)

theorem map : (P.mapIso e.op).hom ≫ TopRestriction.CechTopRestriction.map C U (F.op ⋙ P) ≫
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).hom.f 0 =
      TopRestriction.CechTopRestriction.map D (F.obj ∘ U) P := by
  change P.map e.op.hom ≫
    Pi.lift (fun t : Fin 1 → ι => P.map ((F.map (homOfLE (le_top : (∏ᶜ (U ∘ t)) ≤ ⊤))).op)) ≫
      (Pi.mapIso (fun t : Fin 1 → ι => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)).hom =
    Pi.lift (fun t : Fin 1 → ι => P.map (homOfLE (le_top : (∏ᶜ ((F.obj ∘ U) ∘ t)) ≤ ⊤)).op)
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc]
  erw [Pi.lift_comp_π]
  change P.map _ ≫ P.map _ ≫ P.map _ = P.map _
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

def initialIso : TopRestriction.CechTopRestriction.initial C U (F.op ⋙ P) ≅
    TopRestriction.CechTopRestriction.initial D (F.obj ∘ U) P :=
  ShortComplex.isoMk (P.mapIso e.op).symm
    ((HomologicalComplex.eval A (.up ℕ) 0).mapIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P))
    ((HomologicalComplex.eval A (.up ℕ) 1).mapIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P))
    (by
      change (P.mapIso e.op).inv ≫ TopRestriction.CechTopRestriction.map D (F.obj ∘ U) P = _
      rw [← CechTopRestrictionBaseChange.map F e U P]
      simp only [Iso.inv_hom_id_assoc]
      rfl)
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).hom.comm 0 1)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionBaseChange.CechTopRestrictionBaseChange
