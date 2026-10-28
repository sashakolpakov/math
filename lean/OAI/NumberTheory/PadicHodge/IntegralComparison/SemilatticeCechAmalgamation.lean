import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCone

/-! # Semilattice Cech Amalgamation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SemilatticeCechAmalgamation

noncomputable section

/-! The actual inverse-meet map used by the Čech concatenation prism.
The source coefficient is evaluated on the common intersection. Both
restriction variables are retained, so the construction applies to the
original global-to-open frame-section transformation. -/

open _root_.CategoryTheory Opposite

universe u v w
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A]
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

def map (I V : C) : Q.obj (op (I ⊓ V)) ⟶ (B.obj (op V)).obj (op I) :=
  haveI := h I V
  ((γ.app (op V)).app (op (I ⊓ V))) ≫
    inv ((B.obj (op V)).map (homOfLE (inf_le_left : I ⊓ V ≤ I)).op)

theorem map_restrict (I V : C) : SemilatticeCechAmalgamation.map Q B γ h I V ≫
    (B.obj (op V)).map (homOfLE (inf_le_left : I ⊓ V ≤ I)).op =
      (γ.app (op V)).app (op (I ⊓ V)) := by
  have := h I V
  dsimp only [SemilatticeCechAmalgamation.map]
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem inverse_square {P P' X X' Y Y' : A}
    (a : P ⟶ Y) (a' : P' ⟶ Y') (s : X ⟶ Y) (s' : X' ⟶ Y')
    [IsIso s] [IsIso s'] (f : P ⟶ P') (g : X ⟶ X') (j : Y ⟶ Y')
    (ha : a ≫ j = f ≫ a') (hs : s ≫ j = g ≫ s') :
    (a ≫ inv s) ≫ g = f ≫ a' ≫ inv s' := by
  apply (cancel_mono s').mp
  simpa only [Category.assoc, ← hs, IsIso.inv_hom_id_assoc,
    IsIso.inv_hom_id, Category.comp_id] using ha

theorem naturality {I I' V V' : C} (hi : I' ≤ I) (hv : V' ≤ V) :
    SemilatticeCechAmalgamation.map Q B γ h I V ≫ (B.obj (op V)).map (homOfLE hi).op ≫
        (B.map (homOfLE hv).op).app (op I') =
      Q.map (homOfLE (inf_le_inf hi hv)).op ≫ SemilatticeCechAmalgamation.map Q B γ h I' V' := by
  have := h I V
  have := h I' V'
  let r := (homOfLE (inf_le_inf hi hv)).op
  let j := (B.obj (op V)).map r ≫ (B.map (homOfLE hv).op).app (op (I' ⊓ V'))
  have ha : (γ.app (op V)).app (op (I ⊓ V)) ≫ j =
      Q.map r ≫ (γ.app (op V')).app (op (I' ⊓ V')) := by
    dsimp only [j]
    rw [← Category.assoc, ← (γ.app (op V)).naturality r, Category.assoc]
    have hn := congrArg (fun t => t.app (op (I' ⊓ V'))) (γ.naturality (homOfLE hv).op)
    change 𝟙 _ ≫ (γ.app (op V')).app (op (I' ⊓ V')) =
      (γ.app (op V)).app (op (I' ⊓ V')) ≫
        (B.map (homOfLE hv).op).app (op (I' ⊓ V')) at hn
    rw [Category.id_comp] at hn
    rw [← hn]
    rfl
  have hs : (B.obj (op V)).map (homOfLE (inf_le_left : I ⊓ V ≤ I)).op ≫ j =
      ((B.obj (op V)).map (homOfLE hi).op ≫
        (B.map (homOfLE hv).op).app (op I')) ≫
          (B.obj (op V')).map (homOfLE (inf_le_left : I' ⊓ V' ≤ I')).op := by
    calc
      _ = (B.obj (op V)).map
          ((homOfLE (inf_le_left : I ⊓ V ≤ I)).op ≫ r) ≫
            (B.map (homOfLE hv).op).app (op (I' ⊓ V')) := by
        simp only [j, Functor.map_comp, Category.assoc]
      _ = (B.obj (op V)).map
          ((homOfLE hi).op ≫ (homOfLE (inf_le_left : I' ⊓ V' ≤ I')).op) ≫
            (B.map (homOfLE hv).op).app (op (I' ⊓ V')) := by
        congr 2
      _ = _ := by
        rw [Functor.map_comp, Category.assoc,
          (B.map (homOfLE hv).op).naturality, Category.assoc]
  exact inverse_square _ _ _ _ _ _ j ha hs

theorem global_factorization (I V : C) :
    (γ.app (op V)).app (op I) =
      Q.map (homOfLE (inf_le_left : I ⊓ V ≤ I)).op ≫ SemilatticeCechAmalgamation.map Q B γ h I V := by
  have := h I V
  apply (cancel_mono ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op)).mp
  rw [Category.assoc, map_restrict]
  exact ((γ.app (op V)).naturality
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op).symm

theorem diagonal_factorization (I V : C) :
    (γ.app (op V)).app (op V) ≫
        (GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.cone C V (B.obj (op V)) (fun I => h I V)).app (op I) =
      Q.map (homOfLE (inf_le_right : I ⊓ V ≤ V)).op ≫ SemilatticeCechAmalgamation.map Q B γ h I V := by
  have := h I V
  apply (cancel_mono ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op)).mp
  rw [Category.assoc, Category.assoc, map_restrict,
    GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.app_comp]
  exact ((γ.app (op V)).naturality
    (homOfLE (inf_le_right : I ⊓ V ≤ V)).op).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SemilatticeCechAmalgamation
