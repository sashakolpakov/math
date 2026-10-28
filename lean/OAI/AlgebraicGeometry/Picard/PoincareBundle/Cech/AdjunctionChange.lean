import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant
import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointIsoUnits

/-! # Adjunction Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionChange

noncomputable section

/-!
# Invariant arrows under canonically isomorphic pullback adjunctions
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {R : D ⥤ C} {P Q P' Q' : D ⥤ E} {U V U' V' : E ⥤ D}
  (b : P ⊣ U) (b' : P' ⊣ U') (c : Q ⊣ V) (c' : Q' ⊣ V')
  (α : P ≅ P') (β : Q ≅ Q') (ρ : U ≅ U') (τ : V ≅ V')
  (hP : conjugateEquiv b b' α.inv = ρ.hom) (hQ : conjugateEquiv c c' β.inv = τ.hom)
  (e : U ⋙ R ≅ V ⋙ R)

/-- The direct-image comparison expressed in the new adjunctions. -/
def changedRightIso : U' ⋙ R ≅ V' ⋙ R :=
  Functor.isoWhiskerRight ρ.symm R ≪≫ e ≪≫ Functor.isoWhiskerRight τ R

theorem changedRightIso_square (Z : E) :
    R.map (ρ.hom.app Z) ≫ (changedRightIso ρ τ e).hom.app Z =
      e.hom.app Z ≫ R.map (τ.hom.app Z) := by
  have hm : R.map (ρ.hom.app Z) ≫ R.map (ρ.inv.app Z) = 𝟙 _ := by
    rw [← R.map_comp, Iso.hom_inv_id_app, R.map_id]
  change R.map (ρ.hom.app Z) ≫ (R.map (ρ.inv.app Z) ≫ e.hom.app Z ≫ R.map (τ.hom.app Z)) = _
  rw [← Category.assoc (R.map (ρ.hom.app Z)) (R.map (ρ.inv.app Z)), hm, Category.id_comp]

variable {M : D} (σ : P.obj M ⟶ Q.obj M)

/-- The gluing map expressed in the new left adjoints. -/
def changedGluing : P'.obj M ⟶ Q'.obj M := (α.inv.app M ≫ σ) ≫ β.hom.app M

/-- The corresponding isomorphism between the targets of the invariant diagrams. -/
def targetIso : (V ⋙ R).obj (Q.obj M) ≅ (V' ⋙ R).obj (Q'.obj M) :=
  R.mapIso (τ.app (Q.obj M) ≪≫ V'.mapIso (β.app M))

theorem targetIso_hom : (targetIso (R := R) β τ (M := M)).hom =
    R.map (τ.hom.app (Q.obj M)) ≫ R.map (V'.map (β.hom.app M)) :=
  R.map_comp _ _

/-- The first invariant arrow can be computed by transposing the actual gluing map. -/
theorem leftMap_homEquiv : AdjointCechInvariant.leftMap b e σ = R.map (b.homEquiv M (Q.obj M) σ) ≫ e.hom.app (Q.obj M) := by
  change R.map (b.unit.app M) ≫ e.hom.app (P.obj M) ≫ (V ⋙ R).map σ = _
  rw [b.homEquiv_unit, R.map_comp, Category.assoc]
  exact (congrArg (fun z => R.map (b.unit.app M) ≫ z) (e.hom.naturality σ)).symm

include hP in
/-- The new transposed gluing uses the prescribed mate comparison. -/
theorem changed_homEquiv :
    b'.homEquiv M (Q'.obj M) (changedGluing α β σ) =
      (b.homEquiv M (Q.obj M) σ ≫ ρ.hom.app (Q.obj M)) ≫ U'.map (β.hom.app M) := by
  exact (b'.homEquiv_naturality_right (α.inv.app M ≫ σ) (β.hom.app M)).trans
    (congrArg (fun z => z ≫ U'.map (β.hom.app M))
      (AdjointIsoUnits.homEquiv_transport b b' α ρ hP σ))

include hP in
/-- Both forms of the first invariant arrow agree through the target comparison. -/
theorem leftMap_eq :
    AdjointCechInvariant.leftMap b' (changedRightIso ρ τ e) (changedGluing α β σ) =
      AdjointCechInvariant.leftMap b e σ ≫ (targetIso (R := R) β τ (M := M)).hom := by
  have hn := (changedRightIso ρ τ e).hom.naturality (β.hom.app M)
  change R.map (U'.map (β.hom.app M)) ≫ (changedRightIso ρ τ e).hom.app (Q'.obj M) =
    (changedRightIso ρ τ e).hom.app (Q.obj M) ≫ R.map (V'.map (β.hom.app M)) at hn
  rw [leftMap_homEquiv, changed_homEquiv b b' α β ρ hP σ, R.map_comp, R.map_comp,
    leftMap_homEquiv, targetIso_hom]
  simp only [Category.assoc]
  rw [hn]
  rw [← Category.assoc (R.map (ρ.hom.app (Q.obj M)))
    ((changedRightIso ρ τ e).hom.app (Q.obj M)) (R.map (V'.map (β.hom.app M))),
    changedRightIso_square]
  simp only [Category.assoc]

include hQ in
/-- The adjunction unit is transported through that same target comparison. -/
theorem rightMap_eq :
    AdjointCechInvariant.rightMap (R := R) c' (M := M) =
      AdjointCechInvariant.rightMap (R := R) c ≫ (targetIso (R := R) β τ (M := M)).hom := by
  have hu := AdjointIsoUnits.unit_transport c c' β τ hQ M
  have hm := congrArg (fun z => R.map z) hu
  rw [R.map_comp, R.map_comp] at hm
  change R.map (c'.unit.app M) = R.map (c.unit.app M) ≫ (targetIso (R := R) β τ (M := M)).hom
  rw [targetIso_hom]
  exact hm.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionChange
