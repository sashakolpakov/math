import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedComponentFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContractedAmplePullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedRationalPoints

/-! # Contracted Ample Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContractedAmpleFiniteness

noncomputable section

/-! A proper noetherian scheme mapped affinely into a contracted ample pullback has finitely many points, including nonreduced schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}}

theorem contracted_ample_noetherian_finite (p : X ⟶ Spec (.of K)) [IsProper p] [IsNoetherian X]
    (f : Y ⟶ Z) (u : X ⟶ Y) [IsAffineHom u]
    (a : Spec (.of K) ⟶ Z) (h : u ≫ f = p ≫ a) (L : Line.Bundles.LineBundle Z)
    (hL : (L.pullback f).IsAmple) : Finite X := by
  apply ReducedComponentFiniteness.finite_of_reduced_components_subsingleton X
  intro C hC
  let C' : TopologicalSpace.Closeds X := ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
  let W := ReducedClosedSubschemes.reducedClosedSubscheme X C'
  let i : W ⟶ X := ReducedClosedSubschemes.reducedClosedInclusion X C'
  have : IsClosedImmersion i := ReducedClosedSubschemes.reducedClosedInclusion_isClosedImmersion X C'
  have : IsReduced W := ReducedClosedSubschemes.reducedClosedSubscheme_isReduced X C'
  have : IrreducibleSpace W := ReducedComponentFiniteness.reducedClosedSubscheme_irreducible X C' hC.1
  have : IsProper (i ≫ p) := inferInstance
  obtain ⟨x, hx⟩ := ClosedRationalPoints.nonempty_locallyFiniteType_exists_section (i ≫ p)
  have hc : (i ≫ u) ≫ f = (i ≫ p) ≫ a := by rw [Category.assoc, h, Category.assoc]
  have : IsIso (i ≫ p) := ContractedAmplePullbacks.contracted_ample_pullback_isIso (i ≫ p) x hx f (i ≫ u) a hc L hL
  exact (i ≫ p).isOpenEmbedding.injective.subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContractedAmpleFiniteness
