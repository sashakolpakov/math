import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.LineIsomorphisms
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.IsoPullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Product Line -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine

noncomputable section

/-! A line bundle on a constant group family with a fixed identity-axis
frame. Equal family classes have canonical normalized comparisons. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K]

structure RigidifiedProductLine (A B : Over (Spec (.of K))) [GrpObj A] where
  bundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ A).left
  axis : (Scheme.Modules.pullback (lift (𝟙 B) (1 : B ⟶ A)).left).obj bundle.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left

namespace RigidifiedProductLine

variable {A B : Over (Spec (.of K))} [GrpObj A] (D : RigidifiedProductLine A B)

def line {T : Over (Spec (.of K))} (a : T ⟶ B) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left :=
  D.bundle.pullback (a ⊗ₘ 𝟙 A).left

theorem axis_square {T : Over (Spec (.of K))} (a : T ⟶ B) :
    (lift (𝟙 T) (1 : T ⟶ A)).left ≫ (a ⊗ₘ 𝟙 A).left =
      a.left ≫ (lift (𝟙 B) (1 : B ⟶ A)).left := by
  have h : lift (𝟙 T) (1 : T ⟶ A) ≫ (a ⊗ₘ 𝟙 A) =
      a ≫ lift (𝟙 B) (1 : B ⟶ A) := by simp
  exact congrArg Over.Hom.left h

def frame {T : Over (Spec (.of K))} (a : T ⟶ B) :
    (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj (D.line a).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
  FrameScalar.Construction.rigidificationBaseChangeIso (a ⊗ₘ 𝟙 A).left (lift (𝟙 T) (1 : T ⟶ A)).left
    a.left (lift (𝟙 B) (1 : B ⟶ A)).left (axis_square a) D.bundle.sheaf D.axis

def Normalized {T : Over (Spec (.of K))} (a b : T ⟶ B)
    (e : (D.line a).sheaf ≅ (D.line b).sheaf) : Prop :=
  (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map e.hom ≫ (D.frame b).hom =
    (D.frame a).hom

variable [IsAlgClosed K] [IsProper A.hom] [IsIntegral A.left]

theorem existsUnique_normalized {T : Over (Spec (.of K))} (a b : T ⟶ B)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b)) :
    ∃! e : (D.line a).sheaf ≅ (D.line b).sheaf, D.Normalized a b e := by
  obtain ⟨e⟩ := Quotient.exact h
  obtain ⟨e', he', hu⟩ := LineIsomorphisms.Construction.properConstantFamily_existsUnique_lineIso A.hom (snd T A).left
    (fst T A).left T.hom (IsPullback.of_hasPullback T.hom A.hom).flip
    (lift (𝟙 T) (1 : T ⟶ A)).left (congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A)))
    (D.line a) (D.line b) e (D.frame a ≪≫ (D.frame b).symm)
  have he : ∀ d : (D.line a).sheaf ≅ (D.line b).sheaf,
      D.Normalized a b d ↔
        (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).mapIso d =
          D.frame a ≪≫ (D.frame b).symm := by
    intro d
    constructor
    · intro hd
      dsimp only [RigidifiedProductLine.Normalized] at hd
      apply Iso.ext
      exact (cancel_mono (D.frame b).hom).mp (by
        simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
          Category.assoc, Iso.inv_hom_id, Category.comp_id] using hd)
    · intro hd
      change ((Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).mapIso d).hom ≫ _ = _
      rw [hd]
      simp
  exact ⟨e', (he e').mpr he', fun d hd => hu d ((he d).mp hd)⟩

def comparison {T : Over (Spec (.of K))} (a b : T ⟶ B)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b)) :
    (D.line a).sheaf ≅ (D.line b).sheaf :=
  Classical.choose (D.existsUnique_normalized a b h)

theorem comparison_normalized {T : Over (Spec (.of K))} (a b : T ⟶ B)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b)) :
    D.Normalized a b (D.comparison a b h) :=
  (Classical.choose_spec (D.existsUnique_normalized a b h)).1

theorem comparison_unique {T : Over (Spec (.of K))} (a b : T ⟶ B)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b))
    (e : (D.line a).sheaf ≅ (D.line b).sheaf) (he : D.Normalized a b e) :
    e = D.comparison a b h :=
  (Classical.choose_spec (D.existsUnique_normalized a b h)).2 e he

theorem comparison_self {T : Over (Spec (.of K))} (a : T ⟶ B) :
    D.comparison a a rfl = Iso.refl _ := by
  symm
  apply D.comparison_unique
  dsimp [RigidifiedProductLine.Normalized]
  simp

theorem comparison_comp {T : Over (Spec (.of K))} (a b c : T ⟶ B)
    (hab : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b))
    (hbc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line c)) :
    D.comparison a b hab ≪≫ D.comparison b c hbc = D.comparison a c (hab.trans hbc) := by
  apply D.comparison_unique
  change (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map
    ((D.comparison a b hab).hom ≫ (D.comparison b c hbc).hom) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, D.comparison_normalized b c hbc,
    D.comparison_normalized a b hab]

end RigidifiedProductLine
end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine
