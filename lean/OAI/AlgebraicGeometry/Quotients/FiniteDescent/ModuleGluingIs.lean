import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

/-! # Module Gluing Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleGluingIs.Construction.ModuleGluing

noncomputable section

/-! Gluing local linear maps of module sheaves on a scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

/-- Compatible linear maps on all opens inside each member of an open cover. -/
structure Datum where
  I : Type u
  opens : I → X.Opens
  covers : ∀ x : X, ∃ i, x ∈ opens i
  app : ∀ i (U : X.Opens), U ≤ opens i → Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U)
  naturality : ∀ i {U V : X.Opens} (h : V ≤ U) (hU : U ≤ opens i) (s : Γ(M, U)),
    N.presheaf.map (homOfLE h).op (app i U hU s) =
      app i V (h.trans hU) (M.presheaf.map (homOfLE h).op s)
  overlap : ∀ i j (U : X.Opens) (hi : U ≤ opens i) (hj : U ≤ opens j),
    app i U hi = app j U hj

namespace Datum

variable {M N} (D : Datum M N)

theorem existsUnique_value (U : X.Opens) (s : Γ(M, U)) :
    ∃! t : Γ(N, U), ∀ i,
      N.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op t =
        D.app i (U ⊓ D.opens i) inf_le_right
          (M.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op s) := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  apply F.existsUnique_gluing' (fun i => U ⊓ D.opens i) U (fun _ => homOfLE inf_le_left)
  · intro x hx
    obtain ⟨i, hi⟩ := D.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · intro i j
    let V : X.Opens := (U ⊓ D.opens i) ⊓ (U ⊓ D.opens j)
    change N.presheaf.map (homOfLE (show V ≤ U ⊓ D.opens i from inf_le_left)).op
        (D.app i (U ⊓ D.opens i) inf_le_right
          (M.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op s)) =
      N.presheaf.map (homOfLE (show V ≤ U ⊓ D.opens j from inf_le_right)).op
        (D.app j (U ⊓ D.opens j) inf_le_right
          (M.presheaf.map (homOfLE (show U ⊓ D.opens j ≤ U from inf_le_left)).op s))
    rw [D.naturality, D.naturality,
      D.overlap i j V (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

def value (U : X.Opens) (s : Γ(M, U)) : Γ(N, U) :=
  (D.existsUnique_value U s).choose

theorem value_spec (U : X.Opens) (s : Γ(M, U)) (i : D.I) :
    N.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op (D.value U s) =
      D.app i (U ⊓ D.opens i) inf_le_right
        (M.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op s) :=
  (D.existsUnique_value U s).choose_spec.1 i

theorem value_unique (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U))
    (ht : ∀ i,
      N.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op t =
        D.app i (U ⊓ D.opens i) inf_le_right
          (M.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op s)) :
    t = D.value U s := (D.existsUnique_value U s).choose_spec.2 t ht

theorem value_add (U : X.Opens) (s t : Γ(M, U)) :
    D.value U (s + t) = D.value U s + D.value U t := by
  symm
  apply D.value_unique
  intro i
  simp only [map_add, D.value_spec]

theorem value_smul (U : X.Opens) (r : Γ(X, U)) (s : Γ(M, U)) :
    D.value U (r • s) = r • D.value U s := by
  symm
  apply D.value_unique
  intro i
  rw [N.map_smul, D.value_spec, M.map_smul, map_smul]

theorem value_restrict_subordinate (i : D.I) {U V : X.Opens}
    (h : V ≤ U) (hV : V ≤ D.opens i) (s : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (D.value U s) =
      D.app i V hV (M.presheaf.map (homOfLE h).op s) := by
  have h' : V ≤ U ⊓ D.opens i := le_inf h hV
  calc
    N.presheaf.map (homOfLE h).op (D.value U s) =
        N.presheaf.map (homOfLE h').op
          (N.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op (D.value U s)) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    _ = N.presheaf.map (homOfLE h').op
        (D.app i (U ⊓ D.opens i) inf_le_right
          (M.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op s)) := by
      rw [D.value_spec]
    _ = D.app i V hV (M.presheaf.map (homOfLE h').op
        (M.presheaf.map (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op s)) :=
      D.naturality i h' inf_le_right _
    _ = D.app i V hV (M.presheaf.map (homOfLE h).op s) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl

theorem value_restrict {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (D.value U s) =
      D.value V (M.presheaf.map (homOfLE h).op s) := by
  apply D.value_unique
  intro i
  have h' : V ⊓ D.opens i ≤ U := inf_le_left.trans h
  calc
    N.presheaf.map (homOfLE (show V ⊓ D.opens i ≤ V from inf_le_left)).op
        (N.presheaf.map (homOfLE h).op (D.value U s)) =
      N.presheaf.map (homOfLE h').op (D.value U s) := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
    _ = D.app i (V ⊓ D.opens i) inf_le_right (M.presheaf.map (homOfLE h').op s) :=
      D.value_restrict_subordinate i h' inf_le_right s
    _ = D.app i (V ⊓ D.opens i) inf_le_right
        (M.presheaf.map (homOfLE (show V ⊓ D.opens i ≤ V from inf_le_left)).op
          (M.presheaf.map (homOfLE h).op s)) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl

/-- The actual global morphism of module sheaves obtained by gluing. -/
def glue : M ⟶ N where
  val.app U := ModuleCat.ofHom
    { toFun := D.value U.unop
      map_add' := D.value_add U.unop
      map_smul' := D.value_smul U.unop }
  val.naturality {U V} h := by
    ext s
    exact (D.value_restrict h.unop.le s).symm

theorem glue_spec (i : D.I) (U : X.Opens) (hU : U ≤ D.opens i) (s : Γ(M, U)) :
    D.glue.app U s = D.app i U hU s := by
  have h := D.value_restrict_subordinate i (U := U) le_rfl hU s
  change N.presheaf.map (𝟙 (.op U)) (D.value U s) =
    D.app i U hU (M.presheaf.map (𝟙 (.op U)) s) at h
  rw [N.presheaf.map_id, M.presheaf.map_id] at h
  exact h

theorem glue_unique (a : M ⟶ N)
    (ha : ∀ i (U : X.Opens) (hU : U ≤ D.opens i) (s : Γ(M, U)),
      a.app U s = D.app i U hU s) : a = D.glue := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change a.app U s = D.value U s
  apply D.value_unique
  intro i
  have h := ConcreteCategory.congr_hom
    (a.mapPresheaf.naturality (homOfLE (show U ⊓ D.opens i ≤ U from inf_le_left)).op) s
  exact h.symm.trans (ha i (U ⊓ D.opens i) inf_le_right _)

/-- Local linear isomorphisms glue to a global module-sheaf isomorphism. -/
theorem glue_isIso
    (hD : ∀ i (U : X.Opens) (hU : U ≤ D.opens i), Function.Bijective (D.app i U hU)) :
    IsIso D.glue := by
  apply AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨i, hx⟩ := D.covers x
  refine ⟨D.opens i, hx, ?_⟩
  apply (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff (D.opens i).ι D.glue).mp
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  let W : X.Opens := (D.opens i).ι ''ᵁ V
  have hW : W ≤ D.opens i := by
    rintro _ ⟨y, _, rfl⟩
    exact y.property
  change IsIso (D.glue.app W)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have he : (D.glue.app W : Γ(M, W) → Γ(N, W)) = D.app i W hW :=
    funext (D.glue_spec i W hW)
  rw [he]
  exact hD i W hW

end Datum

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleGluingIs.Construction.ModuleGluing
