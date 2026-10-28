import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme

/-! # Closed Immersion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ClosedImmersion.BundleCycles

noncomputable section

/-! Surjections of modules give the actual closed projective
embeddings of their symmetric algebras. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)

include hf in
theorem symmetricGradedMap_surjective : Function.Surjective (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) := by
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
    exact ⟨algebraMap R (SymmetricAlgebra R M) r,
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)).commutes r⟩
  | ι n =>
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨SymmetricAlgebra.ι R M m, Symmetric.GradedMap.BundleCycles.symmetricGradedMap_generator f m⟩
  | mul a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a * b, map_mul _ a b⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ a b⟩

instance symmetricProjectiveMap_isClosedImmersion : IsClosedImmersion (Scheme.BundleCycles.symmetricProjectiveMap f hf) :=
  Projective.ClosedImmersion.BundleCycles.projectiveMap_isClosedImmersion (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) (Scheme.BundleCycles.symmetricGradedMap_irrelevant f hf)
    (symmetricGradedMap_surjective f hf)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ClosedImmersion.BundleCycles
