import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFrames

/-! # Stabilizers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover

noncomputable section

section

/-! Preserving a full level on every test scheme is equivalent to
fixing the actual base torsion sections. The extension from constant
labels uses naturality on their open fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S : Scheme} {g h N : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}

def torsionPostcomp (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    A.torsionFunctor N ⟶ B.torsionFunctor N where
  app T := GrpCat.ofHom {
    toFun x := ⟨x.val ≫ f, by
      change (x.val ≫ f) ^ N = 1
      rw [← MonObj.pow_comp, show x.val ^ N = 1 from x.property, MonObj.one_comp]⟩
    map_one' := Subtype.ext (MonObj.one_comp f)
    map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val f) }
  naturality {T U} j := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc j.unop x.val f)

def PreservesFullLevel (α : A.FullLevel N) (f : A.scheme ⟶ A.scheme) : Prop :=
  ∀ (T : Over S) (c : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N)),
    (α.hom.app (.op T) c).val ≫ f = (α.hom.app (.op T) c).val

theorem preservesFullLevel_iff_base_torsion (α : A.FullLevel N)
    (f : A.scheme ⟶ A.scheme) [IsMonHom f] :
    PreservesFullLevel α f ↔ ∀ x : A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest S), x.val ≫ f = x.val := by
  constructor
  · intro h x
    obtain ⟨c, hc⟩ := (α.app (.op (ConstantSectionsOn.ConstantSections.baseTest S))).groupIsoToMulEquiv.surjective x
    exact (congrArg (fun y : A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest S) => y.val ≫ f) hc).symm.trans
      ((h (ConstantSectionsOn.ConstantSections.baseTest S) c).trans (congrArg Subtype.val hc))
  · intro h
    have he : α.hom ≫ torsionPostcomp f = α.hom := by
      apply UniversalFrames.LevelCover.torsionNatTrans_ext_on_constants
      intro c
      exact Subtype.ext (h (α.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (LocallyConstant.const S c)))
    intro T c
    have happ := congrArg (fun t : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶
      A.torsionFunctor N => t.app (.op T)) he
    exact congrArg (fun x : A.torsionPoints N T => x.val) (ConcreteCategory.congr_hom happ c)

end

/-! Ordered levels on different abelian schemes are compared on all
test schemes by their constant coefficients over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S : Scheme} {g N : ℕ} {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem level_comparison_of_base_constants (α : A.FullLevel N) (β : B.FullLevel N)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (hf : ∀ c : Frame.Labels.LevelCover.Coefficients g N,
      (α.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (LocallyConstant.const S c)).val ≫ f =
        (β.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (LocallyConstant.const S c)).val)
    (T : Over S) (c : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N)) :
    (α.hom.app (.op T) c).val ≫ f = (β.hom.app (.op T) c).val := by
  have he : α.hom ≫ torsionPostcomp f = β.hom := by
    apply UniversalFrames.LevelCover.torsionNatTrans_ext_on_constants
    intro a
    exact Subtype.ext (hf a)
  have happ := congrArg (fun t : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶
    B.torsionFunctor N => t.app (.op T)) he
  exact congrArg (fun x : B.torsionPoints N T => x.val) (ConcreteCategory.congr_hom happ c)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover
