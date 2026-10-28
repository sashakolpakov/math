import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.ConnectedComponents
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphismLocalSections
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Rigid Parameter Diagonal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidParameterDiagonal

noncomputable section

/-! A parameter whose maps from connected tests are detected by one field-valued point has an open diagonal when its self-product is Noetherian. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def FieldFaithfulParameter {S : Scheme.{u}} (M : Over S) : Prop :=
  ∀ (F : Type u) [Field F] (T : Over S) [PreconnectedSpace T.left]
    (s : Spec (.of F) ⟶ T.left) (a b : T ⟶ M), s ≫ a.left = s ≫ b.left → a = b

theorem fieldFaithfulParameter_open_diagonal {S : Scheme.{u}} (M : Over S)
    [IsNoetherian (pullback M.hom M.hom)] (hM : FieldFaithfulParameter M) :
    IsOpenImmersion (pullback.diagonal M.hom) := by
  let δ := pullback.diagonal M.hom
  apply MonomorphismLocalSections.monomorphism_open_of_local_sections δ
  intro x
  let U := Noetherian.ConnectedComponents.noetherianConnectedComponentOpen (pullback M.hom M.hom) (δ x)
  let V : Over S := Over.mk ((U.ι ≫ pullback.fst M.hom M.hom) ≫ M.hom)
  have : PreconnectedSpace V.left := inferInstanceAs (PreconnectedSpace U.toScheme)
  let a : V ⟶ M := Over.homMk (U.ι ≫ pullback.fst M.hom M.hom) rfl
  let b : V ⟶ M := Over.homMk (U.ι ≫ pullback.snd M.hom M.hom) (by
    change (U.ι ≫ pullback.snd M.hom M.hom) ≫ M.hom = (U.ι ≫ pullback.fst M.hom M.hom) ≫ M.hom
    rw [Category.assoc, Category.assoc, pullback.condition])
  let s₀ := M.left.fromSpecResidueField x ≫ δ
  have hr : Set.range s₀ ⊆ (U : Set (↑(pullback M.hom M.hom) : Type u)) := by
    rintro _ ⟨v, rfl⟩
    change δ (M.left.fromSpecResidueField x v) ∈ connectedComponent (δ x)
    rw [Scheme.fromSpecResidueField_apply]
    exact mem_connectedComponent
  let s : Spec (M.left.residueField x) ⟶ V.left :=
    IsOpenImmersion.lift U.ι s₀ ((Scheme.Opens.range_ι U).symm ▸ hr)
  have hs : s ≫ U.ι = s₀ := IsOpenImmersion.lift_fac _ _ _
  have hsa : s ≫ a.left = M.left.fromSpecResidueField x := by
    change s ≫ (U.ι ≫ pullback.fst M.hom M.hom) = _
    rw [← Category.assoc, hs]
    change (M.left.fromSpecResidueField x ≫ pullback.diagonal M.hom) ≫ pullback.fst M.hom M.hom = _
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hsb : s ≫ b.left = M.left.fromSpecResidueField x := by
    change s ≫ (U.ι ≫ pullback.snd M.hom M.hom) = _
    rw [← Category.assoc, hs]
    change (M.left.fromSpecResidueField x ≫ pullback.diagonal M.hom) ≫ pullback.snd M.hom M.hom = _
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have hab : a = b := hM (M.left.residueField x) V s a b (hsa.trans hsb.symm)
  refine ⟨U, mem_connectedComponent, a.left, ?_⟩
  apply pullback.hom_ext
  · change (a.left ≫ pullback.diagonal M.hom) ≫ pullback.fst M.hom M.hom = _
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    rfl
  · change (a.left ≫ pullback.diagonal M.hom) ≫ pullback.snd M.hom M.hom = _
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
    exact congrArg Over.Hom.left hab

theorem fieldFaithfulParameter_formallyUnramified {S : Scheme.{u}} (M : Over S)
    [IsNoetherian (pullback M.hom M.hom)] (hM : FieldFaithfulParameter M) : FormallyUnramified M.hom := by
  have := fieldFaithfulParameter_open_diagonal M hM
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidParameterDiagonal
