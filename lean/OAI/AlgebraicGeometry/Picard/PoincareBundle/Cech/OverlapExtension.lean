import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Overlap Extension -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.OverlapExtension

noncomputable section

/-!
# Extending the overlap presentation retains the invariant arrows
-/

open _root_.CategoryTheory

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {R : D ⥤ C} {P Q : D ⥤ E} {U V : E ⥤ D} {J : E ⥤ F} {K : F ⥤ E}
  (b : P ⊣ U) (c : Q ⊣ V) (e : U ⋙ R ≅ V ⋙ R) (d : J ⊣ K)

/-- The same direct-image comparison after extending the overlap category. -/
def extendedRightIso : (K ⋙ U) ⋙ R ≅ (K ⋙ V) ⋙ R :=
  NatIso.ofComponents (fun Z => e.app (K.obj Z)) (fun a => e.hom.naturality (K.map a))

theorem extendedRightIso_hom_app (Z : F) :
    (extendedRightIso e (K := K)).hom.app Z = e.hom.app (K.obj Z) := rfl

variable {M : D} (σ : P.obj M ⟶ Q.obj M)

/-- The target map of the two invariant diagrams is induced by the overlap adjunction unit. -/
def targetMap : (V ⋙ R).obj (Q.obj M) ⟶ (V ⋙ R).obj (K.obj (J.obj (Q.obj M))) :=
  (V ⋙ R).map (d.unit.app (Q.obj M))

/-- Extending the overlap postcomposes the first invariant arrow by this one target map. -/
theorem leftMap_eq :
    AdjointCechInvariant.leftMap (Q := Q ⋙ J) (b.comp d) (extendedRightIso e (K := K)) (J.map σ) =
      AdjointCechInvariant.leftMap b e σ ≫ targetMap (R := R) (Q := Q) (V := V) d (M := M) := by
  have he := e.hom.naturality (d.unit.app (P.obj M))
  change R.map (U.map (d.unit.app (P.obj M))) ≫ e.hom.app (K.obj (J.obj (P.obj M))) =
    e.hom.app (P.obj M) ≫ (V ⋙ R).map (d.unit.app (P.obj M)) at he
  have hn : d.unit.app (P.obj M) ≫ K.map (J.map σ) = σ ≫ d.unit.app (Q.obj M) :=
    (d.unit.naturality σ).symm
  have hm := congrArg (fun z => (V ⋙ R).map z) hn
  rw [(V ⋙ R).map_comp, (V ⋙ R).map_comp] at hm
  change R.map ((b.comp d).unit.app M) ≫ e.hom.app (K.obj (J.obj (P.obj M))) ≫
    (V ⋙ R).map (K.map (J.map σ)) =
      (R.map (b.unit.app M) ≫ e.hom.app (P.obj M) ≫ (V ⋙ R).map σ) ≫
        (V ⋙ R).map (d.unit.app (Q.obj M))
  rw [Adjunction.comp_unit_app, R.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (R.map (U.map (d.unit.app (P.obj M))))
    (e.hom.app (K.obj (J.obj (P.obj M)))) ((V ⋙ R).map (K.map (J.map σ))), he]
  simp only [Category.assoc]
  rw [hm]

/-- The other invariant arrow is postcomposed by exactly the same target map. -/
theorem rightMap_eq :
    AdjointCechInvariant.rightMap (R := R) (c.comp d) (M := M) =
      AdjointCechInvariant.rightMap (R := R) c ≫ targetMap (R := R) (Q := Q) (V := V) d (M := M) := by
  change R.map ((c.comp d).unit.app M) = R.map (c.unit.app M) ≫
    (V ⋙ R).map (d.unit.app (Q.obj M))
  rw [Adjunction.comp_unit_app, R.map_comp]
  rfl

/-- A fully faithful extension of overlap coordinates gives an invertible target change. -/
instance targetMap_isIso [J.Full] [J.Faithful] : IsIso (targetMap (R := R) (Q := Q) (V := V) d (M := M)) :=
  inferInstanceAs (IsIso ((V ⋙ R).map (d.unit.app (Q.obj M))))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.OverlapExtension
