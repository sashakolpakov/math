import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Descent Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction

noncomputable section

/-!
# Transport of descent coactions for PoincareBundle

A square commuting with the left adjoints induces a functor on descent
coalgebras. The right-adjoint comparison is its canonical mate; the
counit and coassociativity identities follow from the adjunctions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

universe u v

variable {C D E F : Type u} [Category.{v} C] [Category.{v} D]
  [Category.{v} E] [Category.{v} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G : C ⥤ E} {H : D ⥤ F}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : G ⋙ L₂ ≅ L₁ ⋙ H)

/-- The canonical comparison between right adjoints in the square. -/
def rightMate : R₁ ⋙ G ⟶ H ⋙ R₂ :=
  (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom)).natTrans

/-- The coaction after applying the functor on the covering category. -/
def restrictedCoaction (A : adj₁.toComonad.Coalgebra) :
    H.obj A.A ⟶ adj₂.toComonad.obj (H.obj A.A) :=
  H.map A.a ≫ α.inv.app (R₁.obj A.A) ≫ L₂.map ((rightMate adj₁ adj₂ α).app A.A)

/-- The restricted coaction satisfies the counit equation. -/
theorem restrictedCoaction_counit (A : adj₁.toComonad.Coalgebra) :
    restrictedCoaction adj₁ adj₂ α A ≫ adj₂.counit.app (H.obj A.A) = 𝟙 _ := by
  have h := mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom) A.A
  change L₂.map ((rightMate adj₁ adj₂ α).app A.A) ≫ adj₂.counit.app (H.obj A.A) =
    α.hom.app (R₁.obj A.A) ≫ H.map (adj₁.counit.app A.A) at h
  dsimp only [restrictedCoaction, Adjunction.toComonad_coe, Functor.comp_obj]
  erw [Category.assoc, Category.assoc, h, Iso.inv_hom_id_app_assoc,
    ← H.map_comp, A.counit, H.map_id]

/-- The adjunction unit expressed through the invertible left square
and its canonical right mate. -/
theorem unit_via_rightMate (c : C) :
    adj₂.unit.app (G.obj c) =
      G.map (adj₁.unit.app c) ≫ (rightMate adj₁ adj₂ α).app (L₁.obj c) ≫
        R₂.map (α.inv.app c) := by
  have h := unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom) c
  change G.map (adj₁.unit.app c) ≫ (rightMate adj₁ adj₂ α).app (L₁.obj c) =
    adj₂.unit.app (G.obj c) ≫ R₂.map (α.hom.app c) at h
  erw [← Category.assoc, h, Category.assoc, ← R₂.map_comp,
    Iso.hom_inv_id_app, R₂.map_id, Category.comp_id]

/-- The restricted coaction satisfies the descent cocycle equation. -/
theorem restrictedCoaction_coassoc (A : adj₁.toComonad.Coalgebra) :
    restrictedCoaction adj₁ adj₂ α A ≫ adj₂.toComonad.δ.app (H.obj A.A) =
      restrictedCoaction adj₁ adj₂ α A ≫
        adj₂.toComonad.map (restrictedCoaction adj₁ adj₂ α A) := by
  change (H.map A.a ≫ α.inv.app (R₁.obj A.A) ≫
      L₂.map ((rightMate adj₁ adj₂ α).app A.A)) ≫
        L₂.map (adj₂.unit.app (R₂.obj (H.obj A.A))) =
    (H.map A.a ≫ α.inv.app (R₁.obj A.A) ≫
      L₂.map ((rightMate adj₁ adj₂ α).app A.A)) ≫
        L₂.map (R₂.map (H.map A.a ≫ α.inv.app (R₁.obj A.A) ≫
          L₂.map ((rightMate adj₁ adj₂ α).app A.A)))
  erw [Category.assoc, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => erw [← L₂.map_comp, ← adj₂.unit_naturality]
  erw [unit_via_rightMate adj₁ adj₂ α]
  simp only [Functor.map_comp, Category.assoc]
  erw [← α.inv.naturality_assoc]
  erw [← H.map_comp_assoc, A.coassoc, H.map_comp_assoc]
  erw [α.inv.naturality_assoc]
  erw [← L₂.map_comp_assoc, (rightMate adj₁ adj₂ α).naturality, L₂.map_comp_assoc]
  erw [R₂.map_comp (α.inv.app (R₁.obj A.A))
    (L₂.map ((rightMate adj₁ adj₂ α).app A.A))]
  erw [L₂.map_comp (R₂.map (α.inv.app (R₁.obj A.A)))
    (R₂.map (L₂.map ((rightMate adj₁ adj₂ α).app A.A)))]
  exact congrArg (fun k => H.map A.a ≫ k)
    (Category.assoc (α.inv.app (R₁.obj A.A))
      (L₂.map ((rightMate adj₁ adj₂ α).app A.A))
      (L₂.map (R₂.map (H.map A.a)) ≫
        L₂.map (R₂.map (α.inv.app (R₁.obj A.A))) ≫
          L₂.map (R₂.map (L₂.map ((rightMate adj₁ adj₂ α).app A.A))))).symm

/-- Maps that respect the original coactions respect the restricted ones. -/
theorem restrictedCoaction_naturality {A B : adj₁.toComonad.Coalgebra} (t : A ⟶ B) :
    restrictedCoaction adj₁ adj₂ α A ≫ adj₂.toComonad.map (H.map t.f) =
      H.map t.f ≫ restrictedCoaction adj₁ adj₂ α B := by
  change (H.map A.a ≫ α.inv.app (R₁.obj A.A) ≫
      L₂.map ((rightMate adj₁ adj₂ α).app A.A)) ≫ L₂.map (R₂.map (H.map t.f)) =
    H.map t.f ≫ H.map B.a ≫ α.inv.app (R₁.obj B.A) ≫
      L₂.map ((rightMate adj₁ adj₂ α).app B.A)
  erw [Category.assoc, Category.assoc,
    ← L₂.map_comp ((rightMate adj₁ adj₂ α).app A.A) (R₂.map (H.map t.f)),
    ← (rightMate adj₁ adj₂ α).naturality t.f, L₂.map_comp,
    ← Category.assoc (α.inv.app (R₁.obj A.A)), ← α.inv.naturality,
    Category.assoc, ← Category.assoc (H.map A.a), ← H.map_comp, t.h, H.map_comp,
    Category.assoc]
  rfl

/-- Restriction of descent data is a functor between the coalgebra categories. -/
def coalgebraRestriction : adj₁.toComonad.Coalgebra ⥤ adj₂.toComonad.Coalgebra where
  obj A := {
    A := H.obj A.A
    a := restrictedCoaction adj₁ adj₂ α A
    counit := restrictedCoaction_counit adj₁ adj₂ α A
    coassoc := restrictedCoaction_coassoc adj₁ adj₂ α A }
  map t := {
    f := H.map t.f
    h := restrictedCoaction_naturality adj₁ adj₂ α t }
  map_id A := by
    ext
    exact H.map_id A.A
  map_comp t s := by
    ext
    exact H.map_comp t.f s.f

/-- The restricted datum has precisely the restricted underlying object. -/
theorem coalgebraRestriction_forget :
    coalgebraRestriction adj₁ adj₂ α ⋙ Comonad.forget adj₂.toComonad =
      Comonad.forget adj₁.toComonad ⋙ H := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction
