import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-! # Cohomology Lifts -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts

noncomputable section

/-! Actual local lifts of representatives of degree-one sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

def sheafInjectiveCokernelSequence (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

theorem sheafInjectiveCokernelSequence_shortExact (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (sheafInjectiveCokernelSequence F).ShortExact := by
  dsimp [sheafInjectiveCokernelSequence]
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι F)) }

def sheafInjectiveCokernelBoundary (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (sheafInjectiveCokernelSequence F).X₃.obj.obj (op (⊤ : Opens X)) →+
      CategoryTheory.Sheaf.H F 1 :=
  ((sheafInjectiveCokernelSequence_shortExact F).extClass.postcomp _
    (rfl : 0 + 1 = 1)).comp
      (CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop).symm.toAddMonoidHom

/-- The representative comes from a cokernel of an actual injective embedding. -/
theorem sheafInjectiveCokernelBoundary_surjective (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    Function.Surjective (sheafInjectiveCokernelBoundary F) := by
  intro a
  have : Injective (sheafInjectiveCokernelSequence F).X₂ := by
    dsimp [sheafInjectiveCokernelSequence]
    infer_instance
  obtain ⟨q, hq⟩ := Ext.covariant_sequence_exact₁ _
    (sheafInjectiveCokernelSequence_shortExact F) a (Ext.eq_zero_of_injective _)
    (rfl : 0 + 1 = 1)
  refine ⟨CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop q, ?_⟩
  change ((CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop).symm
    (CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop q)).comp
      (sheafInjectiveCokernelSequence_shortExact F).extClass (rfl : 0 + 1 = 1) = a
  rw [AddEquiv.symm_apply_apply]
  exact hq

/-- A covering family of actual lifts of a global section through a sheaf epimorphism. -/
structure SheafLocalLiftCover {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (q : F ⟶ G) (t : G.obj.obj (op (⊤ : Opens X))) where
  domain : X → Opens X
  mem_domain : ∀ x, x ∈ domain x
  section_ : ∀ x, F.obj.obj (op (domain x))
  image : ∀ x, q.hom.app (op (domain x)) (section_ x) =
    G.obj.map (homOfLE (le_top : domain x ≤ ⊤)).op t

theorem exists_sheafLocalLiftCover {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (q : F ⟶ G) [Epi q] (t : G.obj.obj (op (⊤ : Opens X))) :
    Nonempty (SheafLocalLiftCover q t) := by
  have hq := (TopCat.Presheaf.isLocallySurjective_iff q.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi q).mpr inferInstance)
  have h : ∀ x : X, ∃ U : Opens X, ∃ s : F.obj.obj (op U),
      x ∈ U ∧ q.hom.app (op U) s = G.obj.map (homOfLE (le_top : U ≤ ⊤)).op t := by
    intro x
    obtain ⟨U, hU, ⟨s, hs⟩, hx⟩ := hq ⊤ t x (by trivial)
    exact ⟨U, s, hx, hs⟩
  choose U s hx hs using h
  exact ⟨⟨U, hx, s, hs⟩⟩

def sheafLocalLiftCover {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (q : F ⟶ G) [Epi q] (t : G.obj.obj (op (⊤ : Opens X))) :
    SheafLocalLiftCover q t :=
  Classical.choice (exists_sheafLocalLiftCover q t)

theorem SheafLocalLiftCover.iSup_domain {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    {q : F ⟶ G} {t : G.obj.obj (op (⊤ : Opens X))} (l : SheafLocalLiftCover q t) :
    iSup l.domain = ⊤ := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, l.mem_domain x⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts
