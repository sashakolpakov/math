import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenUnitLocus

/-! # Stalk Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.StalkEquations

noncomputable section

/-! Finitely many equations that vanish in a stalk vanish on one common open
neighborhood. An invertible germ can be made invertible on the same neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem section_restriction_zero_appTop {X : Scheme.{u}} (U : X.Opens)
    (s : Γ(X, ⊤)) (hs : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0) :
    U.ι.appTop s = 0 := by
  have hU : U.ι ''ᵁ ⊤ ≤ U := by simp
  have h := congrArg (X.presheaf.map (homOfLE hU).op) hs
  rw [map_zero] at h
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
    X.presheaf.map (homOfLE hU).op) s = 0 at h
  rw [← X.presheaf.map_comp] at h
  exact h

theorem section_zero_neighborhood {X : Scheme.{u}} (s : Γ(X, ⊤)) (x : X)
    (h : X.presheaf.Γgerm x s = 0) :
    ∃ U : X.Opens, x ∈ U ∧ X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0 := by
  have hz : X.presheaf.germ ⊤ x (by trivial) s =
      X.presheaf.germ ⊤ x (by trivial) 0 := by simpa only [TopCat.Presheaf.Γgerm, map_zero] using h
  obtain ⟨U, hx, a, b, hab⟩ := X.presheaf.germ_eq x (by trivial) (by trivial) s 0 hz
  have ha : a = homOfLE (show U ≤ ⊤ from le_top) := Subsingleton.elim _ _
  exact ⟨U, hx, by simpa only [ha, map_zero] using hab⟩

theorem finite_sections_zero_neighborhood {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (s : ι → Γ(X, ⊤)) (x : X) (h : ∀ i, X.presheaf.Γgerm x (s i) = 0) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ i, X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s i) = 0 := by
  choose V hxV hV using fun i => section_zero_neighborhood (s i) x (h i)
  let U : X.Opens := ⨅ i, V i
  have hx : x ∈ U := by
    change x ∈ ((⨅ i, V i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV
  refine ⟨U, hx, fun i => ?_⟩
  have hi : U ≤ V i := iInf_le V i
  have heq := congrArg (X.presheaf.map (homOfLE hi).op) (hV i)
  rw [map_zero] at heq
  change (X.presheaf.map (homOfLE (show V i ≤ ⊤ from le_top)).op ≫
    X.presheaf.map (homOfLE hi).op) (s i) = 0 at heq
  rw [← X.presheaf.map_comp] at heq
  exact heq

theorem finite_unit_zero_neighborhood {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (t : Γ(X, ⊤)) (s : ι → Γ(X, ⊤)) (x : X)
    (ht : IsUnit (X.presheaf.Γgerm x t)) (hs : ∀ i, X.presheaf.Γgerm x (s i) = 0) :
    ∃ U : X.Opens, x ∈ U ∧ IsUnit (U.ι.appTop t) ∧ ∀ i, U.ι.appTop (s i) = 0 := by
  obtain ⟨V, hxV, hV⟩ := finite_sections_zero_neighborhood s x hs
  let U := V ⊓ X.basicOpen t
  have hxU : x ∈ U := ⟨hxV, (Scheme.mem_basicOpen X t x (by trivial)).mpr ht⟩
  refine ⟨U, hxU, ?_, fun i => ?_⟩
  · apply (OpenUnitLocus.isUnit_appTop_iff_range_subset U.ι t).mpr
    rw [Scheme.Opens.range_ι]
    exact inf_le_right
  · apply section_restriction_zero_appTop U
    have hi : U ≤ V := inf_le_left
    have h := congrArg (X.presheaf.map (homOfLE hi).op) (hV i)
    rw [map_zero] at h
    change (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
      X.presheaf.map (homOfLE hi).op) (s i) = 0 at h
    rw [← X.presheaf.map_comp] at h
    exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.StalkEquations
