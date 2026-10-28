import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Section Division Ne -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionDivisionNe.Construction.SectionDivision

noncomputable section

/-! Division of regular functions detected in the stalks of an integral scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} [IsIntegral X]

theorem restrict_ne_zero {U V : X.Opens} (h : V ≤ U) [Nonempty V]
    {a : Γ(X, U)} (ha : a ≠ 0) : X.presheaf.map (homOfLE h).op a ≠ 0 := by
  intro he
  apply ha
  apply map_injective_of_isIntegral X (homOfLE h)
  simpa only [map_zero] using he

theorem cancel_restrict {U V : X.Opens} (h : V ≤ U) {a : Γ(X, U)} (ha : a ≠ 0)
    {s t : Γ(X, V)}
    (he : X.presheaf.map (homOfLE h).op a * s =
      X.presheaf.map (homOfLE h).op a * t) : s = t := by
  by_cases hV : Nonempty V
  · have := hV
    exact mul_left_cancel₀ (restrict_ne_zero h ha) he
  · have hbot : V = ⊥ := by
      apply SetLike.ext
      intro x
      exact ⟨fun hx => (hV ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, V) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
    exact Subsingleton.elim _ _

theorem exists_local_quotient {U : X.Opens} (a b : Γ(X, U)) (x : U)
    (hx : X.presheaf.germ U x x.2 a ∣ X.presheaf.germ U x x.2 b) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x.1 ∈ V ∧ ∃ c : Γ(X, V),
      X.presheaf.map (homOfLE hVU).op a * c =
        X.presheaf.map (homOfLE hVU).op b := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨V, hVU, hxV, d, hd⟩ := X.presheaf.exists_le_germ_eq c x.2
  refine ⟨V, hVU, hxV, d, ?_⟩
  apply germ_injective_of_isIntegral X x hxV
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, hd]
  exact hc.symm

theorem dvd_of_germs {U : X.Opens} (a b : Γ(X, U)) (ha : a ≠ 0)
    (h : ∀ x : U, X.presheaf.germ U x x.2 a ∣ X.presheaf.germ U x x.2 b) :
    a ∣ b := by
  choose V hVU hxV c hc using fun x => exists_local_quotient a b x (h x)
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcompat : X.presheaf.IsCompatible V c := by
    intro i j
    apply cancel_restrict (inf_le_left.trans (hVU i)) ha
    have hi := congrArg (X.presheaf.map (homOfLE
      (show V i ⊓ V j ≤ V i from inf_le_left)).op) (hc i)
    have hj := congrArg (X.presheaf.map (homOfLE
      (show V i ⊓ V j ≤ V j from inf_le_right)).op) (hc j)
    simp only [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at hi hj
    exact hi.trans hj.symm
  obtain ⟨d, hd, _⟩ := X.sheaf.existsUnique_gluing' V U
    (fun x => homOfLE (hVU x)) hcover c hcompat
  change Γ(X, U) at d
  change ∀ x, X.presheaf.map (homOfLE (hVU x)).op d = c x at hd
  refine ⟨d, ?_⟩
  apply X.sheaf.eq_of_locally_eq' V U (fun x => homOfLE (hVU x)) hcover
  intro x
  change X.presheaf.map (homOfLE (hVU x)).op b =
    X.presheaf.map (homOfLE (hVU x)).op (a * d)
  rw [map_mul, hd]
  exact (hc x).symm

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionDivisionNe.Construction.SectionDivision
