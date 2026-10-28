import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullbackFormula
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedOverlap
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomKernelPair

/-! # Normalized Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedComparison

noncomputable section

/-! The actual normalized comparison exists and agrees on all tests over
the quotient. Its compatibility is proved from target normalizations. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

namespace Construction

theorem tensorPullbackZeroNormalization_eq_square
    {S : Scheme} {H K A B : Over S} [GrpObj H] [GrpObj K]
    (u : H ⟶ K) [IsMonHom u] (v : A ⟶ B) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (K ⊗ B).left)
    (e : (L.pullback (lift (1 : B ⟶ K) (𝟙 B)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) :
    PoincareNormalization.Construction.tensorPullbackZeroNormalization u v L e =
      LinePullbackFormula.Construction.lineSquareNormalization (u ⊗ₘ v) (lift (1 : A ⟶ H) (𝟙 A))
        (lift (1 : B ⟶ K) (𝟙 B)) v (PoincareNormalization.Construction.tensor_dual_zero_slice u v) L.sheaf e := by
  apply Iso.ext
  simp only [PoincareNormalization.Construction.tensorPullbackZeroNormalization, LinePullbackFormula.Construction.lineSquareNormalization,
    LinePullbackFormula.Construction.linePullbackSquareIso, Scheme.Modules.pullbackCongr]
  simp
  rfl

theorem exists_normalized_product_comparison
    {k : Type} [Field k] [IsAlgClosed k] {g h j : ℕ}
    (H : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme j (Spec (.of k))) (f : A.scheme ⟶ B.scheme) [Etale f.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (H.scheme ⊗ B.scheme).left)
    (hLM : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 H.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 H.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
    (l : (L.pullback (lift (1 : B.scheme ⟶ H.scheme) (𝟙 B.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left)
    (m : (M.pullback (lift (1 : B.scheme ⟶ H.scheme) (𝟙 B.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left) :
    let F := LinePullHom.Construction.overSchemeModulePullbacks (Spec (.of k))
    let r := 𝟙 H.scheme ⊗ₘ f
    ∃ a : (F.map r.op.toLoc).toFunctor.obj L.sheaf ≅
        (F.map r.op.toLoc).toFunctor.obj M.sheaf,
      ∀ (T : Over (Spec (.of k))) (p q : T ⟶ H.scheme ⊗ A.scheme)
        (hpq : p ≫ r = q ≫ r),
      pullHom (F := F) a.hom p (p ≫ r) (p ≫ r) rfl rfl =
        pullHom (F := F) a.hom q (p ≫ r) (p ≫ r) hpq.symm hpq.symm := by
  dsimp only
  obtain ⟨a, ha, _⟩ := PoincareNormalization.Construction.normalized_product_pullback_iso H A B f L M hLM l m
  refine ⟨a, ?_⟩
  intro T p q hpq
  apply PullHomKernelPair.Construction.pullHom_compatible_of_kernel_pair (LinePullHom.Construction.overSchemeModulePullbacks (Spec (.of k)))
    (𝟙 H.scheme ⊗ₘ f) a.hom _ p q hpq
  apply NormalizedOverlap.Construction.normalized_product_kernelPair_compatible H A B f L M a.hom (l.hom ≫ m.inv)
  apply LinePullbackFormula.Construction.linePullHom_of_square_normalization
  rw [tensorPullbackZeroNormalization_eq_square,
    tensorPullbackZeroNormalization_eq_square] at ha
  exact ha

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedComparison
