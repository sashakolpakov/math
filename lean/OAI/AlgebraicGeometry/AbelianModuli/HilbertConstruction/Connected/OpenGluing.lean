import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.ConnectednessFieldTests
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Open Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.OpenGluing

noncomputable section

/-! Connected-fiber opens defined on an open cover glue to an open classifying all base changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem fieldPoint_range_subset_iff {K : Type u} [Field K] {S : Scheme.{u}}
    (c : Spec (.of K) ⟶ S) (V : Set S) :
    Set.range c ⊆ V ↔ c (⊥ : PrimeSpectrum K) ∈ V := by
  constructor
  · exact fun h => h ⟨_, rfl⟩
  · rintro h s ⟨k, rfl⟩
    exact (congrArg c (Subsingleton.elim (⊥ : PrimeSpectrum K) k)) ▸ h

theorem geometricallyConnected_open_glue {X S : Scheme.{u}} (p : X ⟶ S)
    (C : S.OpenCover.{v})
    (hC : ∀ i, ∃ U : (C.X i).Opens, ∀ (T : Scheme.{u}) (c : T ⟶ C.X i),
      GeometricallyConnected (pullback.snd (pullback.snd p (C.f i)) c) ↔
        Set.range c ⊆ (U : Set (C.X i))) :
    ∃ U : S.Opens, ∀ (T : Scheme.{u}) (c : T ⟶ S),
      GeometricallyConnected (pullback.snd p c) ↔ Set.range c ⊆ (U : Set S) := by
  choose V hV using hC
  let U : S.Opens := ⨆ i, ((V i).ι ≫ C.f i).opensRange
  have hf : ∀ (K : Type u) [Field K] (c : Spec (.of K) ⟶ S),
      GeometricallyConnected (pullback.snd p c) ↔ Set.range c ⊆ (U : Set S) := by
    intro K _ c
    let k : Spec (.of K) := (⊥ : PrimeSpectrum K)
    have hl (i : C.I₀) (hc : Set.range c ⊆ Set.range (C.f i)) :
        GeometricallyConnected (pullback.snd p c) ↔
          Set.range (IsOpenImmersion.lift (C.f i) c hc) ⊆ (V i : Set (C.X i)) := by
      let b := IsOpenImmersion.lift (C.f i) c hc
      have hb : b ≫ C.f i = c := IsOpenImmersion.lift_fac _ _ _
      exact ((Geometric.ConnectednessFieldTests.geometricallyConnected_iterated_pullback_iff p (C.f i) b).trans
        (by rw [hb])).symm.trans (hV i _ b)
    constructor
    · intro hp
      obtain ⟨i, y, hy⟩ := C.exists_eq (c k)
      have hc : Set.range c ⊆ Set.range (C.f i) :=
        (fieldPoint_range_subset_iff c _).mpr ⟨y, hy⟩
      let b := IsOpenImmersion.lift (C.f i) c hc
      have hb := (hl i hc).mp hp
      apply (fieldPoint_range_subset_iff c _).mpr
      apply (le_iSup (fun i => ((V i).ι ≫ C.f i).opensRange) i)
      refine ⟨⟨b k, hb ⟨k, rfl⟩⟩, ?_⟩
      exact congrArg (fun f : Spec (.of K) ⟶ S => f k) (IsOpenImmersion.lift_fac (C.f i) c hc)
    · intro hcU
      have hk : c k ∈ U := hcU ⟨k, rfl⟩
      obtain ⟨i, z, hz⟩ := (TopologicalSpace.Opens.mem_iSup.mp hk)
      have hc : Set.range c ⊆ Set.range (C.f i) :=
        (fieldPoint_range_subset_iff c _).mpr ⟨z.val, hz⟩
      let b := IsOpenImmersion.lift (C.f i) c hc
      apply (hl i hc).mpr
      apply (fieldPoint_range_subset_iff b _).mpr
      have hb : C.f i (b k) = c k :=
        congrArg (fun f : Spec (.of K) ⟶ S => f k) (IsOpenImmersion.lift_fac (C.f i) c hc)
      have he : b k = z.val := (C.f i).isOpenEmbedding.injective (hb.trans hz.symm)
      exact he ▸ z.property
  exact ⟨U, fun _ c => Geometric.ConnectednessFieldTests.geometricallyConnected_open_field_tests p U hf c⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.OpenGluing
