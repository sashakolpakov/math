import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.TranslationRelation
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.Ampleness.Construction

noncomputable section

/-! Finite group-scheme quotients over an infinite field: the basis
needed for norm affineness is derived from the field, and the kernel
pair is derived from the full kernel functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {K : Type u} [Field K] [Infinite K]

theorem field_quotient_isAmple_of_pullback
    {H R X Y : Scheme.{u}} [PreconnectedSpace Y]
    (q : X ⟶ Y) [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (s t : R ⟶ X) (hk : IsKernelPair q s t)
    (h : H ⟶ Spec (.of K)) [IsFinite h] (a : X ⟶ Spec (.of K)) (r : R ⟶ H)
    (hs : IsPullback r s h a) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (y₀ : Y)
    (hL : (L.pullback q).IsAmple) : L.IsAmple := by
  have : IsAffine H := isAffine_of_isAffineHom h
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  let := h.appTop.hom.toAlgebra
  have : Module.Finite Γ(Spec (.of K), ⊤) Γ(H, ⊤) := h.finite_appTop
  let b := Module.finBasis Γ(Spec (.of K), ⊤) Γ(H, ⊤)
  exact AmpleDescent.Construction.quotient_isAmple_of_pullback_connected q s t hk h a r hs b a L y₀ hL

theorem group_quotient_isAmple_of_pullback
    {A B H : Over (Spec (.of K))} [GrpObj A] [GrpObj B] [PreconnectedSpace B.left]
    (i : H ⟶ A) [Mono i] [IsFinite H.hom]
    (q : A ⟶ B) [IsMonHom q]
    [IsFinite q.left] [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hker : ∀ (T : Over (Spec (.of K))) (x : T ⟶ A),
      x ≫ q = 1 ↔ ∃! z : T ⟶ H, z ≫ i = x)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (hL : (L.pullback q.left).IsAmple) : L.IsAmple := by
  have hk : IsKernelPair q.left (snd H A).left (Quotients.FiniteDescent.Epi.Construction.translation i).left :=
    (Kernel.TranslationRelation.Construction.kernel_translation_isKernelPair i q hker).map (Over.forget (Spec (.of K)))
  have hs : IsPullback (fst H A).left (snd H A).left H.hom A.hom :=
    IsPullback.of_hasPullback H.hom A.hom
  exact field_quotient_isAmple_of_pullback q.left (snd H A).left
    (Quotients.FiniteDescent.Epi.Construction.translation i).left hk H.hom A.hom (fst H A).left hs L
    ((1 : 𝟙_ (Over (Spec (.of K))) ⟶ B).left (IsLocalRing.closedPoint K)) hL

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.Ampleness.Construction
