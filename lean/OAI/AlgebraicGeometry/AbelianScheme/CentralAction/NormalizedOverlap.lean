import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Overlap
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullHom

/-! # Normalized Overlap -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedOverlap.Construction

noncomputable section

/-! Normalization pulled back from the target forces the actual
comparison isomorphism to agree on the entire quotient overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g h j : ℕ}

theorem normalized_product_kernelPair_compatible
    (H : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme j (Spec (.of k))) (f : A.scheme ⟶ B.scheme) [Etale f.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (H.scheme ⊗ B.scheme).left) :
    let F := LinePullHom.Construction.overSchemeModulePullbacks (Spec (.of k))
    let r := 𝟙 H.scheme ⊗ₘ f
    let zA := lift (1 : A.scheme ⟶ H.scheme) (𝟙 A.scheme)
    let zB := lift (1 : B.scheme ⟶ H.scheme) (𝟙 B.scheme)
    ∀ (a : (F.map r.op.toLoc).toFunctor.obj L.sheaf ⟶
        (F.map r.op.toLoc).toFunctor.obj M.sheaf) [IsIso a]
      (b : (F.map zB.op.toLoc).toFunctor.obj L.sheaf ⟶
        (F.map zB.op.toLoc).toFunctor.obj M.sheaf),
      pullHom (F := F) a zA (f ≫ zB) (f ≫ zB)
          (PoincareNormalization.Construction.tensor_dual_zero_slice (𝟙 H.scheme) f) (PoincareNormalization.Construction.tensor_dual_zero_slice (𝟙 H.scheme) f) =
        pullHom (F := F) b f (f ≫ zB) (f ≫ zB) rfl rfl →
      pullHom (F := F) a (pullback.fst r r) (pullback.fst r r ≫ r)
          (pullback.fst r r ≫ r) rfl rfl =
        pullHom (F := F) a (pullback.snd r r) (pullback.fst r r ≫ r)
          (pullback.fst r r ≫ r) pullback.condition.symm pullback.condition.symm := by
  dsimp only
  intro a _ b hn
  let F := LinePullHom.Construction.overSchemeModulePullbacks (Spec (.of k))
  let r := 𝟙 H.scheme ⊗ₘ f
  let zA := lift (1 : A.scheme ⟶ H.scheme) (𝟙 A.scheme)
  let zB := lift (1 : B.scheme ⟶ H.scheme) (𝟙 B.scheme)
  let e := TensorKernelPair.Construction.tensorKernelPairIso H.scheme f
  let zW := lift (1 : pullback f f ⟶ H.scheme) (𝟙 (pullback f f))
  let s := zW ≫ e.inv
  let p := pullback.fst r r
  let q := pullback.snd r r
  let u := pullback.fst f f
  let v := pullback.snd f f
  have hu : s ≫ p = u ≫ zA := by
    rw [Category.assoc, TensorKernelPair.Construction.tensorKernelPairIso_inv_fst]
    exact PoincareNormalization.Construction.tensor_dual_zero_slice (𝟙 H.scheme) u
  have hv : s ≫ q = v ≫ zA := by
    rw [Category.assoc, TensorKernelPair.Construction.tensorKernelPairIso_inv_snd]
    exact PoincareNormalization.Construction.tensor_dual_zero_slice (𝟙 H.scheme) v
  have hz : zA ≫ r = f ≫ zB := PoincareNormalization.Construction.tensor_dual_zero_slice (𝟙 H.scheme) f
  have ht : s ≫ (p ≫ r) = u ≫ f ≫ zB := by
    rw [← Category.assoc, hu, Category.assoc, hz]
  have hs : Function.Injective s.left.appTop := by
    have : IsIso e.inv.left := (Over.forget (Spec (.of k))).map_isIso e.inv
    have : IsIso e.inv.left.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.inv.left.op))
    have hZ := Overlap.Construction.abelian_quotient_overlap_zeroSlice_bijective H A B f
    change Function.Injective (zW ≫ e.inv).left.appTop
    rw [Over.comp_left, Scheme.Hom.comp_appTop]
    exact hZ.1.comp (ConcreteCategory.bijective_of_isIso e.inv.left.appTop).1
  have ha : IsIso (pullHom (F := F) a p (p ≫ r) (p ≫ r) rfl rfl) :=
    PullHomNormalization.Construction.pullHom_isIso F a p (p ≫ r) (p ≫ r) rfl rfl
  apply @LinePullHom.Construction.linePullHom_ext (Spec (.of k)) (H.scheme ⊗ B.scheme) (pullback r r) (pullback f f)
    (p ≫ r) s (u ≫ f ≫ zB) ht hs L M _ _ ha
  exact PullHomNormalization.Construction.pullHom_normalization_overlap F r zA zB f hz a b hn p q pullback.condition
    s u v hu hv pullback.condition

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedOverlap.Construction
