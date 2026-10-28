import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction

/-! # Adjoint Square Factorization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AdjointSquareFactorization

noncomputable section

/-! Local pullback equations become factorizations through the original
adjunction unit whenever the right-adjoint base-change map is invertible. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction

universe u v

variable {C D E F : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E] [Category.{v} F]
variable {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
variable {G : C ⥤ E} {H : D ⥤ F}
variable (adj : L ⊣ R) (adj' : L' ⊣ R') (α : G ⋙ L' ≅ L ⋙ H)

theorem adjunct_square {M N : C} (q : L.obj M ⟶ L.obj N) :
    G.map (adj.homEquiv _ _ q) ≫ (Picard.PoincareBundle.DescentRestriction.rightMate adj adj' α).app (L.obj N) =
      adj'.unit.app (G.obj M) ≫ R'.map (α.hom.app M ≫ H.map q) := by
  let β := Picard.PoincareBundle.DescentRestriction.rightMate adj adj' α
  have hu : G.map (adj.unit.app M) ≫ β.app (L.obj M) =
      adj'.unit.app (G.obj M) ≫ R'.map (α.hom.app M) :=
    unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom) M
  have hn : G.map (R.map q) ≫ β.app (L.obj N) =
      β.app (L.obj M) ≫ R'.map (H.map q) := β.naturality q
  rw [Adjunction.homEquiv_unit, G.map_comp, Category.assoc, hn,
    ← Category.assoc, hu, Category.assoc, ← R'.map_comp]

theorem factorization_of_square [IsIso (Picard.PoincareBundle.DescentRestriction.rightMate adj adj' α)]
    {M N : C} (q : L.obj M ⟶ L.obj N) (c : G.obj M ⟶ G.obj N)
    (hc : L'.map c ≫ α.hom.app N = α.hom.app M ≫ H.map q) :
    c ≫ G.map (adj.unit.app N) = G.map (adj.homEquiv _ _ q) := by
  let β := Picard.PoincareBundle.DescentRestriction.rightMate adj adj' α
  apply (cancel_mono (β.app (L.obj N))).mp
  have hu : G.map (adj.unit.app N) ≫ β.app (L.obj N) =
      adj'.unit.app (G.obj N) ≫ R'.map (α.hom.app N) :=
    unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom) N
  calc
    (c ≫ G.map (adj.unit.app N)) ≫ β.app (L.obj N) =
        (c ≫ adj'.unit.app (G.obj N)) ≫ R'.map (α.hom.app N) := by
      rw [Category.assoc, hu, ← Category.assoc]
    _ = (adj'.unit.app (G.obj M) ≫ R'.map (L'.map c)) ≫ R'.map (α.hom.app N) :=
      congrArg (fun r ↦ r ≫ R'.map (α.hom.app N)) (adj'.unit.naturality c)
    _ = adj'.unit.app (G.obj M) ≫ R'.map (L'.map c ≫ α.hom.app N) := by
      rw [Category.assoc, ← R'.map_comp]
    _ = adj'.unit.app (G.obj M) ≫ R'.map (α.hom.app M ≫ H.map q) :=
      congrArg (fun r ↦ adj'.unit.app (G.obj M) ≫ R'.map r) hc
    _ = G.map (adj.homEquiv _ _ q) ≫ β.app (L.obj N) := (adjunct_square adj adj' α q).symm

theorem transport_factorization
    {C₀ D₀ : Type*} [Category C₀] [Category D₀] {F₀ G₀ : C₀ ⥤ D₀} (e : F₀ ≅ G₀)
    {M N P : C₀} (q : F₀.obj M ⟶ F₀.obj N) (a : N ⟶ P) (b : M ⟶ P)
    (hq : q ≫ F₀.map a = F₀.map b) :
    (e.app M).homCongr (e.app N) q ≫ G₀.map a = G₀.map b := by
  apply (cancel_epi (e.hom.app M)).mp
  change (e.app M).hom ≫ (((e.app M).inv ≫ q ≫ (e.app N).hom) ≫ G₀.map a) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change q ≫ e.hom.app N ≫ G₀.map a = e.hom.app M ≫ G₀.map b
  rw [← e.hom.naturality a, ← Category.assoc, hq, e.hom.naturality b]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AdjointSquareFactorization
