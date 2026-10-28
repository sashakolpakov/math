import OAI.AlgebraicGeometry.Comparison.Betti.PushforwardStalk

/-! # Pushforward Exact -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardExact

noncomputable section

/-! Exactness of the actual direct image along a closed embedding, checked on stalks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits InjectiveFlasque.complexModuleLimits

variable {M N : TopCat.{0}} (f : M ⟶ N)

theorem closedPushforwardStalkZero (hclosed : IsClosed (Set.range f))
    (F : ConstantSheafSections.ComplexSheaves M) (y : N) (hy : y ∉ Set.range f) :
    IsZero ((PushforwardStalk.sheafStalk N y).obj ((TopologicalSheafPullback.sheafDirectImage f).obj F)) := by
  let P : N.Presheaf (ModuleCat.{0} ℂ) := ((TopologicalSheafPullback.sheafDirectImage f).obj F).obj
  let Ft : TopCat.Sheaf (ModuleCat.{0} ℂ) M := F
  let U : Opens N := ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩
  have hyU : y ∈ U := hy
  change IsZero (P.stalk y)
  rw [IsZero.iff_id_eq_zero]
  apply P.stalk_hom_ext
  intro V hyV
  simp only [Category.comp_id, comp_zero]
  have hempty : (Opens.map f).obj (V ⊓ U) = ⊥ := by
    ext x
    constructor
    · intro hx
      change f x ∈ V ∧ f x ∉ Set.range f at hx
      exact (hx.2 ⟨x, rfl⟩).elim
    · intro hx
      exact hx.elim
  have hz : IsZero (P.obj (op (V ⊓ U))) := (Ft.isTerminalOfEqEmpty hempty).isZero
  have hw : P.germ (V ⊓ U) y ⟨hyV, hyU⟩ = 0 := hz.eq_of_src _ _
  have hr := P.germ_res (homOfLE inf_le_left : V ⊓ U ⟶ V) y ⟨hyV, hyU⟩
  exact hr.symm.trans (by rw [hw, comp_zero])

theorem closedPushforward_map_exact (hf : Topology.IsInducing f) (hclosed : IsClosed (Set.range f))
    (S : ShortComplex (ConstantSheafSections.ComplexSheaves M)) (hS : S.Exact) : (S.map (TopologicalSheafPullback.sheafDirectImage f)).Exact := by
  let T : ShortComplex (ConstantSheafSections.ComplexSheaves N) := S.map (TopologicalSheafPullback.sheafDirectImage f)
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (show ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) N) from T)).mpr
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    have hs : (S.map (PushforwardStalk.sheafStalk M x)).Exact :=
      (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
        (show ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) M) from S)).mp hS x
    exact (ShortComplex.exact_iff_of_iso (S.mapNatIso (PushforwardStalk.pushforwardStalkIso f hf x))).mpr hs
  · exact ShortComplex.exact_of_isZero_X₂ _ (closedPushforwardStalkZero f hclosed S.X₂ y hy)

theorem closedPushforwardExact (hf : Topology.IsInducing f) (hclosed : IsClosed (Set.range f)) :
    PreservesFiniteLimits (TopologicalSheafPullback.sheafDirectImage f) ∧ PreservesFiniteColimits (TopologicalSheafPullback.sheafDirectImage f) :=
  ((TopologicalSheafPullback.sheafDirectImage f).exact_tfae.out 2 4).mp (closedPushforward_map_exact f hf hclosed)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardExact
