import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PushforwardSheafStalk

/-! # Closed Pushforward Exactness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedPushforwardExactness.Constructions

noncomputable section

/-! Closed-embedding pushforward preserves exactness of genuine sheaf complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X Y : TopCat.{0}} (f : Y ⟶ X)
variable (hf : Topology.IsClosedEmbedding f)

include hf

theorem closedPushforwardSheaf_stalk_isZero (F : TopCat.Sheaf (ModuleCat.{0} R) Y)
    (x : X) (hx : x ∉ Set.range f) :
    IsZero (((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).obj F).presheaf.stalk x) := by
  let O : Opens X := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro s
  obtain ⟨U,hU,hxU,t,rfl⟩ :=
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).obj F).presheaf).exists_le_germ_eq s
      (show x∈O from hx)
  have he : (Opens.map f).obj U = ⊥ := by
    apply le_antisymm
    · intro y hy
      exact False.elim ((hU hy) ⟨y,rfl⟩)
    · exact bot_le
  have hz : IsZero (F.obj.obj (op ((Opens.map f).obj U))) :=
    (F.isTerminalOfEqEmpty he).isZero
  have : Subsingleton (F.obj.obj (op ((Opens.map f).obj U))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  have ht : t=0 := @Subsingleton.elim (F.obj.obj (op ((Opens.map f).obj U))) _ t 0
  rw [ht, map_zero]

theorem closedPushforwardSheafComplex_stalk_exactAt
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ)
    (x : X) (hx : x ∉ Set.range f) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (PushforwardSheafStalk.Constructions.moduleSheafPushforwardComplex f K) x).ExactAt n :=
  HomologicalComplex.ExactAt.of_isZero (closedPushforwardSheaf_stalk_isZero f hf (K.X n) x hx)

theorem closedPushforwardSheafComplex_exactAt
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ) (n : ℕ) (hK : K.ExactAt n) :
    (PushforwardSheafStalk.Constructions.moduleSheafPushforwardComplex f K).ExactAt n := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    ((PushforwardSheafStalk.Constructions.moduleSheafPushforwardComplex f K).sc n)).mpr
  intro x
  by_cases hx : x∈Set.range f
  · obtain ⟨y,rfl⟩ := hx
    have hs : (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K y).ExactAt n :=
      (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (K.sc n)).mp hK y
    exact hs.of_iso (PushforwardSheafStalk.Constructions.pushforwardSheafStalkComplexIso f hf.isEmbedding.isInducing K y).symm
  · exact closedPushforwardSheafComplex_stalk_exactAt f hf K x hx n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedPushforwardExactness.Constructions
