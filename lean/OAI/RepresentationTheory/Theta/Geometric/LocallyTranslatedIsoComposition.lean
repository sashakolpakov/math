import OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedIsoNaturality
import OAI.RepresentationTheory.Theta.Geometric.TranslatedLineIsoComposition
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Locally Translated Iso Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedIsoComposition

noncomputable section

/-! A coherent family of translation comparisons retains its
composition law after gluing over locally constant label fibers. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
universe u

theorem locallyTranslatedIso_comp {X T : Scheme.{u}} (M : X.Modules)
    {I : Type u} [Mul I] (t : I → (X ⟶ X)) (ht : ∀ a b, t a ≫ t b = t (a * b))
    (e : ∀ a, (Scheme.Modules.pullback (t a)).obj M ≅ M)
    (he : ∀ a b, ((Scheme.Modules.pullbackCongr (ht a b)).app M).symm ≪≫
      Normalized.PullbackComposition.composePullbackIso (t a) (t b) (e a) (e b) = e (a * b))
    (c d : LocallyConstant T I) (x y z : T ⟶ X)
    (hxy : ∀ a, (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι ≫ y = ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι ≫ x) ≫ t a)
    (hyz : ∀ a, (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι ≫ z = ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι ≫ y) ≫ t a)
    (hxz : ∀ a, (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (c * d) a).ι ≫ z =
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (c * d) a).ι ≫ x) ≫ t a)
    (φ : (Scheme.Modules.pullback y).obj M ⟶ (Scheme.Modules.pullback x).obj M)
    (ψ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback y).obj M)
    (χ : (Scheme.Modules.pullback z).obj M ⟶ (Scheme.Modules.pullback x).obj M)
    (hφ : ∀ a, (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι).map φ =
      (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M (t a) (e a) x y (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a) (hxy a)).hom)
    (hψ : ∀ a, (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι).map ψ =
      (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M (t a) (e a) y z (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a) (hyz a)).hom)
    (hχ : ∀ a, (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (c * d) a).ι).map χ =
      (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M (t a) (e a) x z (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (c * d) a) (hxz a)).hom) :
    ψ ≫ φ = χ := by
  let pair : LocallyConstant T (I × I) :=
    ⟨fun v => (c v, d v), c.isLocallyConstant.prodMk d.isLocallyConstant⟩
  apply Intrinsic.PullbackCoherence.nativePullback_ext_open_cover _ χ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber pair) (by
    apply top_unique
    intro v _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨pair v, rfl⟩)
  rintro ⟨a, b⟩
  let U := AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber pair (a, b)
  have hc : ∀ v : U.toScheme, c (U.ι v) = a := fun v => congrArg Prod.fst v.property
  have hd : ∀ v : U.toScheme, d (U.ι v) = b := fun v => congrArg Prod.snd v.property
  have hcd : ∀ v : U.toScheme, (c * d) (U.ι v) = a * b :=
    fun v => congrArg₂ (· * ·) (hc v) (hd v)
  let sc := LocallyConstantFiberMap.locallyConstantFiberLift U.ι c a hc
  let sd := LocallyConstantFiberMap.locallyConstantFiberLift U.ι d b hd
  let scd := LocallyConstantFiberMap.locallyConstantFiberLift U.ι (c * d) (a * b) hcd
  have hsc := LocallyConstantFiberMap.locallyConstantFiberLift_fac U.ι c a hc
  have hsd := LocallyConstantFiberMap.locallyConstantFiberLift_fac U.ι d b hd
  have hscd := LocallyConstantFiberMap.locallyConstantFiberLift_fac U.ι (c * d) (a * b) hcd
  have h₁ := LocallyConstantFiberMap.translated_relation_of_factor (t a) x y _ (hxy a) U.ι sc hsc
  have h₂ := LocallyConstantFiberMap.translated_relation_of_factor (t b) y z _ (hyz b) U.ι sd hsd
  have h₃ := LocallyConstantFiberMap.translated_relation_of_factor (t (a * b)) x z _ (hxz (a * b)) U.ι scd hscd
  have hφ' := Intrinsic.TranslatedRestrictions.nativePullback_glued_translation_of_factor M (t a) (e a) x y _ (hxy a)
    φ (hφ a) U.ι sc hsc (U.ι ≫ x) (U.ι ≫ y) rfl rfl h₁
  have hψ' := Intrinsic.TranslatedRestrictions.nativePullback_glued_translation_of_factor M (t b) (e b) y z _ (hyz b)
    ψ (hψ b) U.ι sd hsd (U.ι ≫ y) (U.ι ≫ z) rfl rfl h₂
  have hχ' := Intrinsic.TranslatedRestrictions.nativePullback_glued_translation_of_factor M (t (a * b)) (e (a * b)) x z _ (hxz (a * b))
    χ (hχ (a * b)) U.ι scd hscd (U.ι ≫ x) (U.ι ≫ z) rfl rfl h₃
  rw [Intrinsic.PullbackCoherence.nativePullback_comp ψ φ U.ι (U.ι ≫ z) (U.ι ≫ y) (U.ι ≫ x) rfl rfl rfl, hψ', hφ', hχ']
  exact TranslatedLineIsoComposition.translatedMapLineIso_comp_of_eq M (t a) (t b) (t (a * b)) (ht a b)
    (e a) (e b) (e (a * b)) (he a b) _ _ _ h₁ h₂ h₃

end

end OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedIsoComposition
