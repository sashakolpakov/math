import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PicardClassIso
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.IsoPullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Rigidified Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction

noncomputable section

/-! A rigidified line on a relative group family has canonical
comparisons over Noetherian parameters whenever its relative Picard values agree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

structure RelativeRigidifiedProductLine {S : Scheme.{0}} (A B : Over S) [GrpObj A] where
  bundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ A).left
  axis : (Scheme.Modules.pullback (lift (𝟙 B) (1 : B ⟶ A)).left).obj bundle.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left

namespace RelativeRigidifiedProductLine

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] (D : RelativeRigidifiedProductLine A B)

def line {T : Over S} (a : T ⟶ B) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left := D.bundle.pullback (a ⊗ₘ 𝟙 A).left

theorem axis_square {T : Over S} (a : T ⟶ B) :
    (lift (𝟙 T) (1 : T ⟶ A)).left ≫ (a ⊗ₘ 𝟙 A).left =
      a.left ≫ (lift (𝟙 B) (1 : B ⟶ A)).left := by
  have h : lift (𝟙 T) (1 : T ⟶ A) ≫ (a ⊗ₘ 𝟙 A) = a ≫ lift (𝟙 B) (1 : B ⟶ A) := by simp
  exact congrArg Over.Hom.left h

def frame {T : Over S} (a : T ⟶ B) :
    (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj (D.line a).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
  FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (a ⊗ₘ 𝟙 A).left (lift (𝟙 T) (1 : T ⟶ A)).left
    a.left (lift (𝟙 B) (1 : B ⟶ A)).left (axis_square a) D.bundle.sheaf D.axis

def relativeValue {T : Over S} (a : T ⟶ B) :=
  (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a))

def Normalized {T : Over S} (a b : T ⟶ B) (e : (D.line a).sheaf ≅ (D.line b).sheaf) : Prop :=
  (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map e.hom ≫ (D.frame b).hom =
    (D.frame a).hom

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]

set_option backward.isDefEq.respectTransparency false in
theorem existsUnique_normalized {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) :
    ∃! e : (D.line a).sheaf ≅ (D.line b).sheaf, D.Normalized a b e := by
  have : IsProper (fst T A).left := inferInstanceAs (IsProper (pullback.fst T.hom A.hom))
  have : Smooth (fst T A).left := inferInstanceAs (Smooth (pullback.fst T.hom A.hom))
  have : GeometricallyConnected (fst T A).left :=
    inferInstanceAs (GeometricallyConnected (pullback.fst T.hom A.hom))
  let σ := (lift (𝟙 T) (1 : T ⟶ A)).left
  have hσ : σ ≫ (fst T A).left = 𝟙 T.left := congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A))
  have hLM : Nonempty ((D.line a).sheaf ≅ (D.line b).sheaf) :=
    Noetherian.PicardClassIso.Construction.noetherian_bundleIso_of_relativePicard_eq A T (D.line a) (D.line b) σ hσ
      (D.frame a ≪≫ (D.frame b).symm) h
  obtain ⟨e, he, hu⟩ := Noetherian.BundleNormalization.Construction.noetherian_existsUnique_bundleIso_with_section_fiber (fst T A).left σ hσ
    (D.line a) (D.line b) hLM (D.frame a ≪≫ (D.frame b).symm)
  have hn (d : (D.line a).sheaf ≅ (D.line b).sheaf) : D.Normalized a b d ↔
      (Scheme.Modules.pullback σ).map d.hom = (D.frame a ≪≫ (D.frame b).symm).hom := by
    constructor
    · intro hd
      dsimp only [RelativeRigidifiedProductLine.Normalized] at hd
      exact (cancel_mono (D.frame b).hom).mp (by
        simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hd)
    · intro hd
      change (Scheme.Modules.pullback σ).map d.hom ≫ (D.frame b).hom = (D.frame a).hom
      rw [hd]
      simp
  exact ⟨e, (hn e).mpr he, fun d hd => hu d ((hn d).mp hd)⟩

def comparison {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) : (D.line a).sheaf ≅ (D.line b).sheaf :=
  Classical.choose (D.existsUnique_normalized a b h)

theorem comparison_normalized {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) : D.Normalized a b (D.comparison a b h) :=
  (Classical.choose_spec (D.existsUnique_normalized a b h)).1

theorem comparison_unique {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) (e : (D.line a).sheaf ≅ (D.line b).sheaf)
    (he : D.Normalized a b e) : e = D.comparison a b h :=
  (Classical.choose_spec (D.existsUnique_normalized a b h)).2 e he

theorem comparison_self {T : Over S} [IsLocallyNoetherian T.left] (a : T ⟶ B) :
    D.comparison a a rfl = Iso.refl _ := by
  symm
  apply D.comparison_unique
  simp [RelativeRigidifiedProductLine.Normalized]

theorem comparison_comp {T : Over S} [IsLocallyNoetherian T.left] (a b c : T ⟶ B)
    (hab : D.relativeValue a = D.relativeValue b) (hbc : D.relativeValue b = D.relativeValue c) :
    D.comparison a b hab ≪≫ D.comparison b c hbc = D.comparison a c (hab.trans hbc) := by
  apply D.comparison_unique
  change (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map
    ((D.comparison a b hab).hom ≫ (D.comparison b c hbc).hom) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, D.comparison_normalized b c hbc, D.comparison_normalized a b hab]

end RelativeRigidifiedProductLine

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction
