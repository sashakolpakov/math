import OAI.AlgebraicGeometry.SheafCohomology.IrreducibleStep

/-! # Vanishing Grothendieck Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open _root_.CategoryTheory.Limits _root_.Opposite

set_option backward.isDefEq.respectTransparency false

namespace Projective

open OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

/-!
# Grothendieck's vanishing theorem

Grothendieck's vanishing theorem (Hartshorne III.2.7): for a Noetherian topological space `X`
of dimension `n` and any sheaf `F` of abelian groups on `X`, `Hⁱ(X, F) = 0` for all `i > n`.

## Main results

* `GrothendieckVanishing` — the headline theorem.
* `reducible_vanishing` — reduction to the irreducible case.
* `grothendieck_vanishing_of_irreducible` — the irreducible-case wrapper that performs the
 base-case split between `dim X = 0` and `dim X > 0`.

The dimension-zero base case is proved here; the positive-dimensional irreducible step
lives in `IrreducibleStep.lean`.
-/

universe u

open Limits

/-! ## Reduction to irreducible spaces -/

theorem reducible_vanishing
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)
    (_ : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      [IrreducibleSpace Y] (G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  suffices ∀ (s : Finset (Set X)),
      (∀ Z ∈ s, Z ∈ irreducibleComponents X) →
      ∀ (Gsh : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X),
      (∀ x : X, x ∉ ⋃₀ (s : Set (Set X)) →
        ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj Gsh.obj),
        a = 0) →
      Subsingleton (Sheaf.H Gsh n) by
    exact this hfin.toFinset (by simp) F (fun x hx ↦ absurd (by
      simpa [Set.Finite.toFinset] using Set.mem_sUnion.mp
        (sUnion_irreducibleComponents (X := (↑X : Type u)) ▸ Set.mem_univ x)) hx)
  intro s; induction s using Finset.induction_on with
  | empty =>
    intro _ Gsh hG_stalks
    exact API.ProjectiveVanishing.sheafH_subsingleton_of_isZero
      (API.ProjectiveVanishing.sheaf_isZero_of_zero_stalks X Gsh.property (fun x a ↦ hG_stalks x (by simp) a)) n
  | @insert Z s' hZ_notin ih =>
    intro hs_irred Gsh hG_stalks
    have hZ_comp := hs_irred Z (Finset.mem_insert_self Z s')
    have hZ_closed := isClosed_of_mem_irreducibleComponents Z hZ_comp
    let GZ := ((Vanishing.Projective.TopCat.Sheaf.pullback AddCommGrpCat.{u} (ClosedImmersion.ProjectiveVanishing.TopCat.closedIncl hZ_closed)).obj Gsh)
    let S := ClosedImmersion.ProjectiveVanishing.closedImmersionSES (Z := Z) (hZ := hZ_closed) Gsh
    have hSE := ClosedImmersion.ProjectiveVanishing.closedImmersionSES_shortExact (Z := Z) (hZ := hZ_closed) Gsh
    have hker : Subsingleton (Sheaf.H S.X₁ n) :=
      ih (fun Z' hZ' ↦ hs_irred Z' (Finset.mem_insert_of_mem hZ')) S.X₁ fun x hx a ↦ by
        by_cases hxZ : x ∈ Z
        · -- closedIncl_unit_stalk_isIso: iso on stalks at z ∈ Z
          have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.hom) := by
            exact
              (ClosedImmersion.ProjectiveVanishing.TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrpCat.{u})
                (hs := hZ_closed) Gsh ⟨x, hxZ⟩)
          exact API.ProjectiveVanishing.stalk_zero_of_ses_g_iso S hSE x inferInstance a
        · exact API.ProjectiveVanishing.stalk_zero_of_shortExact_kernel S hSE x (hG_stalks x (by
            simpa only [Finset.coe_insert, Set.sUnion_insert, Set.mem_union, not_or] using ⟨hxZ, hx⟩)) a
    exact ClosedImmersionCohomology.ProjectiveVanishing.subsingleton_sheafH_of_closedImmersion_middle
      (Z := Z) (hZ := hZ_closed) Gsh n hker
      (by
        have : IrreducibleSpace (TopCat.of Z) := isIrreducible_iff_irreducibleSpace.mp hZ_comp.1
        exact ih_irred (TopCat.of Z) GZ
          (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Z)
          (TopologicalKrullDim.ProjectiveVanishing.topologicalKrullDim_subspace_lt_of_lt (X := (↑X : Type u)) Z hn))

private theorem irreducible_dim_zero_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (hdim : topologicalKrullDim X ≤ 0) :
    Subsingleton (Sheaf.H F n) := by
  have hFlasque : FlasqueVanishing.Projective.IsFlasqueSheaf F := fun {U V} i ↦ by
    rcases TopologicalKrullDim.ProjectiveVanishing.opens_eq_bot_or_top_of_irreducibleSpace_dim_zero hdim U with rfl | rfl
    · exact (Vanishing.Projective.TopCat.Sheaf.isTerminalOfEmpty _ F).isZero.epi _
    · have hV := le_antisymm le_top (homOfLE le_top ≫ i |>.le); subst hV
      rw [Subsingleton.elim i (𝟙 ⊤), op_id, F.obj.map_id]; infer_instance
  have hn_ne : n ≠ 0 := fun h ↦ by
    subst h; exact absurd hn (not_lt.mpr TopologicalKrullDim.ProjectiveVanishing.topologicalKrullDim_nonneg)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
  exact FlasqueVanishing.Projective.sheafH_subsingleton_of_flasque X F hFlasque m

theorem grothendieck_vanishing_of_irreducible
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih_irred : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      [IrreducibleSpace Y] (m : ℕ) (G : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H F n) := by
  by_cases hEmpty : IsEmpty X
  · let := hEmpty
    simpa using API.ProjectiveVanishing.sheafH_subsingleton_of_isEmpty F n
  · rw [not_isEmpty_iff] at hEmpty
    by_cases hIrred : IrreducibleSpace X
    · exact ih_irred X n F le_rfl hn
    · exact reducible_vanishing X n hn F hIrred
        (fun Y [_] [_] G hle hY ↦ ih_irred Y n G hle hY)

/-! ## Main theorem -/

/-- **Grothendieck's vanishing theorem** (Hartshorne III, Theorem 2.7). -/
theorem GrothendieckVanishing (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (h : n > topologicalKrullDim X)
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) :
    Subsingleton (Sheaf.H F n) := by
  have hwf : WellFounded (fun (a b : WithBot ℕ∞) ↦ a < b) := wellFounded_lt
  exact hwf.induction (C := fun d ↦
    ∀ (X : TopCat.{u}) [NoetherianSpace X]
      (n : ℕ) (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X),
      topologicalKrullDim X = d → n > d →
        Subsingleton (Sheaf.H F n))
    (topologicalKrullDim X) (fun d ih X _ n F hd hn ↦ by
      -- Reduce to irreducible X
      exact
        grothendieck_vanishing_of_irreducible X n (hd ▸ hn) F
          (fun Y _ _ m G hle hY ↦ by
            by_cases hposY : topologicalKrullDim Y > 0
            · exact IrreducibleStep.ProjectiveVanishing.irreducible_pos_vanishing (F := G.obj) G.property hposY m hY
                (by
                  intro Z _ m' G' hG' hlt hm'
                  exact ih (topologicalKrullDim Z) (lt_of_lt_of_le hlt (hd ▸ hle))
                    Z m' ⟨G', hG'⟩ rfl hm')
            · exact irreducible_dim_zero_vanishing G m hY (le_of_not_gt hposY)))
    X n F rfl h
end Projective

end OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing
