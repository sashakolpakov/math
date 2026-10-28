import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Represented Intersection Transfer -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedIntersectionTransfer

noncomputable section

/-! Transfer a represented intersection between two monic natural
transformations, retaining the exact inclusion compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {B M : Over S}
variable {F G : (Over S)ᵒᵖ ⥤ Type u}

theorem representedIntersectionTransfer
    (t : yoneda.obj B ⟶ F) [Mono t] (g : G ⟶ F) [Mono g]
    (j : M ⟶ B) [Mono j]
    (h : ∀ (T : Over S) (a : T ⟶ B),
      (∃ v : G.obj (.op T), g.app (.op T) v = t.app (.op T) a) ↔
        ∃ b : T ⟶ M, b ≫ j = a) :
    ∃ e : yoneda.obj M ≅ ((Subfunctor.range t).preimage g).toFunctor,
      e.hom ≫ ((Subfunctor.range t).preimage g).ι ≫ g = yoneda.map j ≫ t := by
  have hv (T : Over S) (b : T ⟶ M) :
      ∃ v : G.obj (.op T), g.app (.op T) v = t.app (.op T) (b ≫ j) :=
    (h T (b ≫ j)).mpr ⟨b, rfl⟩
  choose v hv using hv
  have hg (T : (Over S)ᵒᵖ) : Function.Injective (g.app T) :=
    (CategoryTheory.mono_iff_injective _).mp inferInstance
  have ht (T : (Over S)ᵒᵖ) : Function.Injective (t.app T) :=
    (CategoryTheory.mono_iff_injective _).mp inferInstance
  let k : yoneda.obj M ⟶ ((Subfunctor.range t).preimage g).toFunctor := {
    app T := ↾fun b => ⟨v T.unop b, ⟨b ≫ j, (hv T.unop b).symm⟩⟩
    naturality T U a := by
      apply ConcreteCategory.hom_ext
      intro b
      apply Subtype.ext
      apply hg U
      change g.app U (v U.unop (a.unop ≫ b)) = g.app U (G.map a (v T.unop b))
      rw [hv, NatTrans.naturality_apply g a, hv]
      have hn := ConcreteCategory.congr_hom (t.naturality a) (show T.unop ⟶ B from b ≫ j)
      change t.app U (a.unop ≫ (b ≫ j)) = F.map a (t.app T (b ≫ j)) at hn
      simpa only [Category.assoc] using hn }
  have hk : IsIso k := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro T
    apply (isIso_iff_bijective _).mpr
    constructor
    · intro b c he
      apply (cancel_mono j).mp
      apply ht T
      rw [← hv, ← hv]
      exact congrArg (fun x => g.app T x.val) he
    · intro z
      obtain ⟨a, ha⟩ := z.property
      obtain ⟨b, hb⟩ := (h T.unop a).mp ⟨z.val, ha.symm⟩
      refine ⟨b, Subtype.ext (hg T ?_)⟩
      change g.app T (v T.unop b) = g.app T z.val
      rw [hv, hb]
      exact ha
  let := hk
  refine ⟨asIso k, ?_⟩
  ext T b
  exact hv T.unop b

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedIntersectionTransfer
