import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrderedInjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CoverCoefficients

/-! # Single Supported Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleSupportedCover

noncomputable section

/-! The canonical support extension has its original global Cech image.
All coordinate changes use the actual single-sheaf augmentation to its
chosen injective resolution, including on the original global cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem conjugate {D : Type*} [Category D] {A B C E F G : D}
    (eL : A ≅ B) (eG : C ≅ E) (fL : F ≅ B) (fG : G ≅ E)
    (a : A ⟶ C) (b : B ⟶ E) (c : F ⟶ G)
    (h₁ : a ≫ eG.hom = eL.hom ≫ b) (h₂ : fL.hom ≫ b = c ≫ fG.hom) :
    c = (eL ≪≫ fL.symm).inv ≫ a ≫ (eG ≪≫ fG.symm).hom := by
  apply (cancel_mono fG.hom).mp
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₁, Iso.inv_hom_id_assoc]
  exact h₂.symm

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates
variable {X : Scheme.{0}} [X.IsSeparated] {C : Type} [Preorder C] [HasFiniteProducts C]
  (F₁ F₂ : C ⥤ X.Opens) {ι κ ν μ ρ : Type}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F₁]
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F₂]
  (O₁ O₂ : X.Opens) (H : InjectiveIntegerRows.SingleSupportedCandidate.Conditions F₁ F₂ W O₁ O₂)
  (N : X.Modules) [N.IsQuasicoherent] (c : ℕ)
  (B : κ → X.Opens) (J : ν → X.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F₁.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → X.Opens) (hV : ∀ j, IsAffineOpen (V j)) (T : ρ → X.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F₁.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (hB : ∀ j, B j ≤ O₁) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (F₁.obj (⊤_ C)) B J s
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q)]
  [IsIso (RelativeCech.Refinement.homology (F₁.obj (⊤_ C)) B J s
    (Affine.OrderedInjective.Comparison.integerPresheaf N c) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (Affine.OrderedInjective.Comparison.integerPresheaf N c)) q)]

def originalComparison :
    (AffinePrincipal.Injective.Comparison.source F₁ W N c).homology q ⟶
    (Affine.OrderedInjective.Comparison.source N c V).homology q :=
  PresheafCover.Comparison.comparison F₁ W B J r s V T l t
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q

omit [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F₂] in
private theorem coordinates :
    originalComparison F₁ W N c B J r s V T l t q =
      (InjectiveIntegerCoordinates.bridge F₁ W N c H.wide_affine q).inv ≫
      InjectiveIntegerCoordinates.forget.map (PresheafCover.Comparison.comparison F₁ W B J r s V T l t
        (Affine.OrderedInjective.Comparison.integerPresheaf N c) q) ≫
      (Affine.OrderedInjective.Comparison.bridge N c V hV q).hom := by
  let : IsIso (RelativeCech.Refinement.homology (F₁.obj (⊤_ C)) B J s
      (Affine.OrderedInjective.Comparison.targetPresheaf N c) q) :=
    Presheaf.CoverCoefficients.relative_isIso InjectiveIntegerCoordinates.forget
      (Affine.OrderedInjective.Comparison.integerPresheaf N c) (F₁.obj (⊤_ C)) B J s q
  let : IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
      (Affine.OrderedInjective.Comparison.targetPresheaf N c)) q) :=
    Presheaf.CoverCoefficients.ordered_isIso InjectiveIntegerCoordinates.forget
      (Affine.OrderedInjective.Comparison.integerPresheaf N c) V T t q
  have hc := Presheaf.CoverCoefficients.principal InjectiveIntegerCoordinates.forget
    (Affine.OrderedInjective.Comparison.integerPresheaf N c) F₁ W B J r s V T l t q
  have hn := PresheafCover.Comparison.naturality F₁ W B J r s V T l t
    (Affine.OrderedInjective.Comparison.augmentation N c) q
  exact conjugate (InjectiveIntegerCoordinates.coefficientIso F₁ W N c q)
    (Affine.OrderedInjective.Comparison.coefficientIso N c V q)
    (AffinePrincipal.Injective.Comparison.homologyIso F₁ W N c H.wide_affine q)
    (Affine.OrderedInjective.Comparison.homologyIso N c V hV q)
    _ _ _ hc hn

include hB in
omit [X.IsSeparated] [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F₂] [N.IsQuasicoherent] [IsIso (RelativeCech.Refinement.homology (F₁.obj (⊤_ C)) B J s (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q)] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q)] in
private theorem integer_comparison :
    PresheafCover.Comparison.comparison F₁ W B J r s V T l t
      (Affine.OrderedInjective.Comparison.integerPresheaf N c) q =
    H.moduleForget N c q ≫ homologyMap (Presheaf.OrderedCechEdge.edge V
      (Affine.OrderedInjective.Comparison.integerPresheaf N c)) q := by
  let : IsIso (RelativeCech.Refinement.homology (F₁.obj (⊤_ C)) B J s
      (Relative.SupportedExtension.underlying ℤ X (InjectiveIntegerCoordinates.complex N c)) q) :=
    (inferInstance : IsIso (RelativeCech.Refinement.homology (F₁.obj (⊤_ C)) B J s
      (Affine.OrderedInjective.Comparison.integerPresheaf N c) q))
  let : IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
      (Relative.SupportedExtension.underlying ℤ X (InjectiveIntegerCoordinates.complex N c))) q) :=
    (inferInstance : IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
      (Affine.OrderedInjective.Comparison.integerPresheaf N c)) q))
  exact SupportedCover.Comparison.comparison ℤ X (InjectiveIntegerCoordinates.complex N c) F₁ W B J r s V T l t O₁
    H.wide_punctured hB H.wide_global q H.wide_cover
    (InjectiveIntegerRows.exactAt_succ F₁ W N c)

include hB in
omit [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F₂] in
theorem comparison :
    originalComparison F₁ W N c B J r s V T l t q =
      H.forgetSupport N c q ≫ Affine.OrderedInjective.Comparison.coverOutput N c V hV q := by
  have h := coordinates F₁ F₂ W O₁ O₂ H N c B J r s V hV T l t q
  rw [integer_comparison F₁ F₂ W O₁ O₂ H N c B J r s V T l t hB q,
    CategoryTheory.Functor.map_comp] at h
  simpa only [InjectiveIntegerRows.SingleSupportedCandidate.Conditions.forgetSupport,
    Affine.OrderedInjective.Comparison.coverOutput, Category.assoc, Iso.hom_inv_id_assoc] using h

include hB in
theorem candidate_global :
    H.candidate N c q ≫ originalComparison F₁ W N c B J r s V T l t q =
      H.selectedExtension N c q ≫ Affine.OrderedInjective.Comparison.coverOutput N c V hV q := by
  rw [comparison F₁ F₂ W O₁ O₂ H N c B J r s V hV T l t hB q,
    ← Category.assoc, H.candidate_global]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleSupportedCover
