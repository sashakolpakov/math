import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalSheafIs

/-! # Rational Regularity Local -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalRegularityLocal.Construction.RationalRegularity

noncomputable section

/-! Rational functions regular at every point of an open set are actual regular sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} [IsIntegral X]

theorem scalarMap_injective (U : X.Opens) : Function.Injective (RationalSheafIs.Construction.RationalSheaf.scalarMap U) := by
  intro a b hab
  by_cases hU : Nonempty U
  · have := hU
    exact X.germToFunctionField_injective U (congrFun hab ⟨hU⟩)
  · have hbot : U = ⊥ := by
      apply SetLike.ext
      intro x
      exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
    exact Subsingleton.elim _ _

theorem exists_local_section {U : X.Opens} (r : RationalSheafIs.Construction.RationalSheaf.sections U) (x : U)
    (hx : ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = r ⟨⟨x⟩⟩) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x.1 ∈ V ∧ ∃ s : Γ(X, V),
      RationalSheafIs.Construction.RationalSheaf.scalarMap V s = RationalSheafIs.Construction.RationalSheaf.restrict hVU r := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨V, hVU, hxV, s, hs⟩ := X.presheaf.exists_le_germ_eq a x.2
  refine ⟨V, hVU, hxV, s, ?_⟩
  funext hv
  have : Nonempty V := hv.down
  change X.germToFunctionField V s = _
  rw [← X.algebraMap_germ_eq_germToFunctionField hxV s, hs]
  exact ha

theorem exists_section {U : X.Opens} (r : RationalSheafIs.Construction.RationalSheaf.sections U)
    (h : ∀ x : U, ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = r ⟨⟨x⟩⟩) :
    ∃ s : Γ(X, U), RationalSheafIs.Construction.RationalSheaf.scalarMap U s = r := by
  choose V hVU hxV s hs using fun x => exists_local_section r x (h x)
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcompat : X.presheaf.IsCompatible V s := by
    intro i j
    apply scalarMap_injective (V i ⊓ V j)
    change RationalSheafIs.Construction.RationalSheaf.scalarMap (V i ⊓ V j)
      (X.presheaf.map (homOfLE (show V i ⊓ V j ≤ V i from inf_le_left)).op (s i)) =
      RationalSheafIs.Construction.RationalSheaf.scalarMap (V i ⊓ V j)
        (X.presheaf.map (homOfLE (show V i ⊓ V j ≤ V j from inf_le_right)).op (s j))
    rw [← RationalSheafIs.Construction.RationalSheaf.scalar_restrict (show V i ⊓ V j ≤ V i from inf_le_left) (s i),
      ← RationalSheafIs.Construction.RationalSheaf.scalar_restrict (show V i ⊓ V j ≤ V j from inf_le_right) (s j), hs i, hs j]
    rfl
  obtain ⟨t, ht, _⟩ := X.sheaf.existsUnique_gluing' V U
    (fun x => homOfLE (hVU x)) hcover s hcompat
  change Γ(X, U) at t
  change ∀ x, X.presheaf.map (homOfLE (hVU x)).op t = s x at ht
  refine ⟨t, ?_⟩
  funext hu
  let x : U := hu.down.some
  have he := congrArg (RationalSheafIs.Construction.RationalSheaf.scalarMap (V x)) (ht x)
  rw [← RationalSheafIs.Construction.RationalSheaf.scalar_restrict, hs x] at he
  exact congrFun he ⟨⟨⟨x.1, hxV x⟩⟩⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalRegularityLocal.Construction.RationalRegularity
