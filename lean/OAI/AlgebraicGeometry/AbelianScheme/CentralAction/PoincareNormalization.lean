import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ZeroSliceScalars
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualQuotientPolarization
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Poincare Normalization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoincareNormalization.Construction

noncomputable section

/-! Actual zero-slice normalizations of Poincare bundles are preserved
by the constructed group maps and their tensor products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {H K A B : Over S} [GrpObj H] [GrpObj K]

theorem tensor_dual_zero_slice (u : H ⟶ K) [IsMonHom u] (v : A ⟶ B) :
    lift (1 : A ⟶ H) (𝟙 A) ≫ (u ⊗ₘ v) = v ≫ lift (1 : B ⟶ K) (𝟙 B) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

/-- A normalization on the second factor pulls back through a group
map in the first factor and an arbitrary map in the second factor. -/
def tensorPullbackZeroNormalization (u : H ⟶ K) [IsMonHom u] (v : A ⟶ B)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (K ⊗ B).left)
    (e : (L.pullback (lift (1 : B ⟶ K) (𝟙 B)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) :
    ((L.pullback (u ⊗ₘ v).left).pullback
      (lift (1 : A ⟶ H) (𝟙 A)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left :=
  (Scheme.Modules.pullbackComp (lift (1 : A ⟶ H) (𝟙 A)).left (u ⊗ₘ v).left).app L.sheaf ≪≫
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (tensor_dual_zero_slice u v))).app L.sheaf ≪≫
  ((Scheme.Modules.pullbackComp v.left (lift (1 : B ⟶ K) (𝟙 B)).left).app L.sheaf).symm ≪≫
  (Scheme.Modules.pullback v.left).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso v.left

theorem abelian_zeroSlice_global_function_bijective
    {k : Type} [Field k] [IsAlgClosed k] {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))) :
    Function.Bijective (lift (1 : B.scheme ⟶ A.scheme) (𝟙 B.scheme)).left.appTop := by
  have : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  have : IsReduced A.scheme.left :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field A.scheme.hom
  have : Smooth (A.scheme ⊗ B.scheme).hom := by dsimp; infer_instance
  have : IsReduced (A.scheme ⊗ B.scheme).left :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field (A.scheme ⊗ B.scheme).hom
  exact ZeroSliceScalars.Construction.zeroSlice_global_function_bijective A.scheme B.scheme η[A.scheme]

/-- Equal raw line-bundle classes on a product of abelian varieties have
a unique isomorphism respecting specified identity-slice normalizations. -/
theorem abelian_product_normalized_line_iso
    {k : Type} [Field k] [IsAlgClosed k] {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.scheme ⊗ B.scheme).left)
    (hLM : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)
    (l : (L.pullback (lift (1 : B.scheme ⟶ A.scheme) (𝟙 B.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left)
    (m : (M.pullback (lift (1 : B.scheme ⟶ A.scheme) (𝟙 B.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left) :
    ∃! a : L.sheaf ≅ M.sheaf,
      (Scheme.Modules.pullback (lift (1 : B.scheme ⟶ A.scheme) (𝟙 B.scheme)).left).map
        a.hom ≫ m.hom = l.hom :=
  NormalizedLineIso.Construction.existsUnique_normalized_line_iso _ (abelian_zeroSlice_global_function_bijective A B)
    L M (Quotient.exact hLM) l m

/-- The comparison on the quotient cover can be normalized using the
trivializations pulled back from the target. Retaining their origin is
what permits comparison on the full quotient overlap. -/
theorem normalized_product_pullback_iso
    {k : Type} [Field k] [IsAlgClosed k] {g h j : ℕ}
    (H : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (P : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
    (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme j (Spec (.of k))) (f : P.scheme ⟶ Q.scheme)
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (H.scheme ⊗ Q.scheme).left)
    (hLM : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 H.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 H.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M))
    (l : (L.pullback (lift (1 : Q.scheme ⟶ H.scheme) (𝟙 Q.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Q.scheme.left)
    (m : (M.pullback (lift (1 : Q.scheme ⟶ H.scheme) (𝟙 Q.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Q.scheme.left) :
    ∃! a : (L.pullback (𝟙 H.scheme ⊗ₘ f).left).sheaf ≅
        (M.pullback (𝟙 H.scheme ⊗ₘ f).left).sheaf,
      (Scheme.Modules.pullback (lift (1 : P.scheme ⟶ H.scheme) (𝟙 P.scheme)).left).map
          a.hom ≫ (tensorPullbackZeroNormalization (𝟙 H.scheme) f M m).hom =
        (tensorPullbackZeroNormalization (𝟙 H.scheme) f L l).hom :=
  abelian_product_normalized_line_iso H P
    (L.pullback (𝟙 H.scheme ⊗ₘ f).left) (M.pullback (𝟙 H.scheme ⊗ₘ f).left)
    hLM (tensorPullbackZeroNormalization (𝟙 H.scheme) f L l)
    (tensorPullbackZeroNormalization (𝟙 H.scheme) f M m)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoincareNormalization.Construction
