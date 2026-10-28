import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Local Immersion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LocalImmersion.ProperLocalImmersion

noncomputable section

/-! Recognize closed immersions from properness and local graph charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u v

theorem immersion_of_open_coordinate {Z U X P Q : Scheme.{u}}
    (a : Z ⟶ U) (g : Z ⟶ P) (i : U ⟶ X)
    (c : U ⟶ Q) [IsOpenImmersion c] (r : P ⟶ Q) (h : a ≫ c = g ≫ r)
    [IsImmersion (prod.lift (a ≫ i) g)] : IsImmersion g := by
  let k := pullback.lift a g h
  let t : pullback c r ⟶ X ⨯ P := prod.lift (pullback.fst c r ≫ i) (pullback.snd c r)
  have hkt : k ≫ t = prod.lift (a ≫ i) g := by
    apply prod.hom_ext <;>
      simp only [k, t, Category.assoc, prod.lift_fst, prod.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd]
  have : IsImmersion (k ≫ t) := by rw [hkt]; infer_instance
  have : IsImmersion k := IsImmersion.of_comp k t
  have he : g = k ≫ pullback.snd c r := (pullback.lift_snd _ _ _).symm
  rw [he]
  infer_instance

theorem closed_of_chart_cover {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {ι : Type v} (V : ι → Y.Opens) (hV : ∀ x : X, ∃ i, f x ∈ V i)
    (hi : ∀ i, IsImmersion ((f ⁻¹ᵁ V i).ι ≫ f)) : IsClosedImmersion f := by
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨i, hx⟩ := hV x
    have hy : f y ∈ V i := hxy ▸ hx
    have := hi i
    have he : ((f ⁻¹ᵁ V i).ι ≫ f) (⟨x, hx⟩ : (f ⁻¹ᵁ V i).toScheme) =
        ((f ⁻¹ᵁ V i).ι ≫ f) (⟨y, hy⟩ : (f ⁻¹ᵁ V i).toScheme) := hxy
    exact congrArg Subtype.val (((f ⁻¹ᵁ V i).ι ≫ f).isEmbedding.injective he)
  have : SurjectiveOnStalks f := by
    constructor
    intro x
    obtain ⟨i, hx⟩ := hV x
    have := hi i
    let x' : (f ⁻¹ᵁ V i).toScheme := ⟨x, hx⟩
    have hs := ((f ⁻¹ᵁ V i).ι ≫ f).stalkMap_surjective x'
    rw [Scheme.Hom.stalkMap_comp] at hs
    intro s
    obtain ⟨r, hr⟩ := hs ((f ⁻¹ᵁ V i).ι.stalkMap x' s)
    refine ⟨r, ?_⟩
    exact (ConcreteCategory.bijective_of_isIso ((f ⁻¹ᵁ V i).ι.stalkMap x')).1 hr
  exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    f.continuous hinj f.isClosedMap⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LocalImmersion.ProperLocalImmersion
