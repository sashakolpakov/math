import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Open Immersion Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenImmersionCriterion

noncomputable section

/-! Cartesian pieces that are isomorphisms onto target opens assemble to an open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem isOpenImmersion_of_cartesian_isomorphism_pieces {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type v} (V U : ι → Scheme.{u}) (a : ∀ i, V i ⟶ X) (b : ∀ i, U i ⟶ Y)
    (p : ∀ i, V i ⟶ U i) [∀ i, IsOpenImmersion (a i)] [∀ i, IsOpenImmersion (b i)]
    [∀ i, IsIso (p i)] (H : ∀ i, IsPullback (a i) (p i) f (b i))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (a i)) : IsOpenImmersion f := by
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨i, v, rfl⟩ := hcover x
    have hp : f (a i v) = b i (p i v) :=
      congrArg (fun q : V i ⟶ Y => q v) (H i).w
    obtain ⟨w, hw, hwp⟩ := Scheme.exists_preimage_of_isPullback (H i) y (p i v) (hxy.symm.trans hp)
    exact (congrArg (a i) ((p i).isOpenEmbedding.injective hwp)).symm.trans hw
  apply IsOpenImmersion.of_forall_source_exists f hinj
  intro x
  obtain ⟨i, hi⟩ := hcover x
  refine ⟨V i, a i, inferInstance, hi, ?_⟩
  have hp : IsOpenImmersion (p i ≫ b i) := inferInstance
  exact (congrArg (fun q : V i ⟶ Y => IsOpenImmersion q) (H i).w).mpr hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenImmersionCriterion
