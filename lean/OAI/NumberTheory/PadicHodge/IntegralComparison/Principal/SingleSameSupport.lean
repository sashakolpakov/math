import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsRestrictionIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalSupportCover

/-! # Single Same Support -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleSameSupport

noncomputable section

/-! Restriction between affine diagrams containing the same support is
inverse to the canonical supported candidate. Every original class has
the same global comparison after restriction, without a scalar condition. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem iso_of_triangle {D : Type*} [Category D] {A B C : D}
    (a : A ⟶ B) (b : A ⟶ C) (r : B ⟶ C) [IsIso a] [IsIso b]
    (h : a ≫ r = b) : IsIso r := by
  have hr : r = inv a ≫ b := by
    apply (cancel_epi a).mp
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using h
  rw [hr]
  infer_instance

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates
variable {X : Scheme.{0}} {C : Type} [Preorder C] [HasFiniteProducts C]
  (F G : C ⥤ X.Opens) (α : G ⟶ F) {ι : Type} [LinearOrder ι] (W : ι → C)
  [∀ (d : ℕ) (a : Fin (d+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  [∀ (d : ℕ) (a : Fin (d+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G]
  (O : X.Opens) (H : InjectiveIntegerRows.SingleSupportedCandidate.Conditions F G W O O)
  (N : X.Modules) [N.IsQuasicoherent] (c q : ℕ)

include H in
omit [N.IsQuasicoherent] in
theorem module_restriction_isIso : IsIso (homologyMap (InjectiveIntegerCoordinates.restriction F W N c G α) q) := by
  let : IsIso (Supported.OrderedCechRestriction.sourceMap ℤ X F G α O (InjectiveIntegerCoordinates.complex N c)) :=
    Supported.SectionsRestrictionIso.complex_isIso O (F.obj (⊤_ C)) (G.obj (⊤_ C))
      (leOfHom (α.app (⊤_ C))) H.wide_global H.local_global (InjectiveIntegerCoordinates.complex N c)
  let := Supported.OrderedCech.Comparison.quasiIso ℤ X F W O (InjectiveIntegerCoordinates.complex N c)
    H.wide_punctured H.wide_cover (InjectiveIntegerRows.exactAt_succ F W N c)
  let := Supported.OrderedCech.Comparison.quasiIso ℤ X G W O (InjectiveIntegerCoordinates.complex N c)
    H.local_punctured H.local_cover (InjectiveIntegerRows.exactAt_succ G W N c)
  exact iso_of_triangle _ _ _
    (Supported.OrderedCechRestriction.homology ℤ X F G α W O (InjectiveIntegerCoordinates.complex N c)
      H.wide_punctured H.local_punctured q)

include H in
theorem restriction_isIso :
    IsIso (homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) q) := by
  let := module_restriction_isIso F G α W O H N c q
  exact iso_of_triangle (InjectiveIntegerCoordinates.bridge F W N c H.wide_affine q).hom
    (InjectiveIntegerCoordinates.forget.map (homologyMap (InjectiveIntegerCoordinates.restriction F W N c G α) q) ≫ (InjectiveIntegerCoordinates.bridge G W N c H.local_affine q).hom)
    _ (InjectiveIntegerCoordinates.bridge_restriction F W N c G α H.wide_affine H.local_affine q).symm

theorem restriction_candidate :
    homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) q ≫
      H.candidate N c q = 𝟙 _ := by
  let := restriction_isIso F G α W O H N c q
  apply (cancel_mono (homologyMap
    (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) q)).mp
  rw [Category.assoc, H.candidate_restriction N c α q, Category.comp_id, Category.id_comp]

variable [X.IsSeparated] {μ : Type} [LinearOrder μ] (V : μ → X.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))

theorem comparison :
    homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) q ≫
      CanonicalSupportCover.comparison G W O H.selected.wide_affine
        H.selected.wide_punctured H.selected.wide_cover H.selected.wide_global N c V hV haV q =
    CanonicalSupportCover.comparison F W O H.wide_affine H.wide_punctured
      H.wide_cover H.wide_global N c V hV haV q := by
  rw [← CanonicalSupportCover.candidate_comparison F W O N c V hV haV q G O H,
    ← Category.assoc, restriction_candidate F G α W O H N c q, Category.id_comp]

theorem recovery (x : (AffinePrincipal.Injective.Comparison.source F W N c).homology q) :
    CanonicalSupportCover.comparison F W O H.wide_affine H.wide_punctured
      H.wide_cover H.wide_global N c V hV haV q x =
    CanonicalSupportCover.comparison G W O H.selected.wide_affine
      H.selected.wide_punctured H.selected.wide_cover H.selected.wide_global N c V hV haV q
      (homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) q x) :=
  (ConcreteCategory.congr_hom (comparison F G α W O H N c q V hV haV) x).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleSameSupport
