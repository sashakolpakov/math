import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineSections

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w z

section Adjunction
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Faithful]

theorem rightAdjoint_map_epi (adj : F ⊣ G) {M N : D}
    [IsIso (adj.counit.app M)] [IsIso (adj.counit.app N)] (f : M ⟶ N) [Epi f] :
    Epi (G.map f) := by
  have h : Epi (F.map (G.map f) ≫ adj.counit.app N) := by
    change Epi ((G ⋙ F).map f ≫ adj.counit.app N)
    rw [adj.counit.naturality f]
    infer_instance
  exact F.epi_of_epi_map ((epi_comp_iff_of_isIso _ _).mp h)

end Adjunction

variable (R : CommRingCat.{u}) {M N : (Spec R).Modules}

theorem gamma_map_epi [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] : Epi ((moduleSpecΓFunctor (R := R)).map f) := by
  let : IsIso ((tilde.adjunction (R := R)).counit.app M) := by
    change IsIso M.fromTildeΓ
    infer_instance
  let : IsIso ((tilde.adjunction (R := R)).counit.app N) := by
    change IsIso N.fromTildeΓ
    infer_instance
  exact rightAdjoint_map_epi (tilde.adjunction (R := R)) f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineSections
