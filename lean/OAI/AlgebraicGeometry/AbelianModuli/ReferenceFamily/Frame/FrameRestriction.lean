import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IndependentFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LevelFamilies

/-! # Frame Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover

noncomputable section

/-! Compatibility with HilbertConstruction's actual geometric restriction of full
levels. Classifying frames commute with changes of test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem relativeCoefficients_left (T : Over S)
    (α : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶ (A.pullback T.hom).torsionFunctor N)
    (c : Labels.LevelCover.Coefficients g N) :
    (IndependentFrames.LevelCover.relativeCoefficients A T α c).val.left =
      (α.app (.op (ConstantSectionsOn.ConstantSections.baseTest T.left)) (LocallyConstant.const T.left c)).val.left ≫
        pullback.fst A.scheme.hom T.hom :=
  IndependentFrames.LevelCover.relativePointEquiv_left A T T (𝟙 T) _

theorem pullbackCongrIso_hom_left_fst {B : Scheme.{0}} (f h : B ⟶ S) (w : f = h) :
    (A.pullbackCongrIso f h w).hom.left ≫ pullback.fst A.scheme.hom h =
      pullback.fst A.scheme.hom f := by
  subst h
  exact Category.id_comp _

theorem level_mappedIdentity_left {B C : Scheme.{0}} {d : ℕ}
    (D : HilbertConstruction.Abelian.Schemes.AbelianScheme d B) (α : D.FullLevel N) (f : C ⟶ B)
    (c : Multiplicative (Fin (2 * d) → ZMod N)) :
    (α.hom.app (.op ((Over.map f).obj (ConstantSectionsOn.ConstantSections.baseTest C))) (LocallyConstant.const C c)).val.left =
      (α.hom.app (.op (Over.mk f)) (LocallyConstant.const C c)).val.left := by
  let j : Over.mk f ⟶ (Over.map f).obj (ConstantSectionsOn.ConstantSections.baseTest C) :=
    Over.homMk (𝟙 C) ((Category.id_comp _).trans (Category.id_comp _))
  have hn := ConcreteCategory.congr_hom (α.hom.naturality j.op) (LocallyConstant.const C c)
  have hleft := congrArg (fun x : D.torsionPoints N (Over.mk f) => x.val.left) hn
  exact ((Category.id_comp _).symm.trans hleft.symm)

/-- Geometric restriction preserves the actual coefficient sections
after forgetting the change of base. -/
theorem relativeCoefficients_restrict {T U : Over S} (j : T ⟶ U)
    (α : (A.pullback U.hom).FullLevel N) (c : Labels.LevelCover.Coefficients g N) :
    IndependentFrames.LevelCover.relativeCoefficients A T (α.restrict j).hom c =
      A.torsionPullback N j (IndependentFrames.LevelCover.relativeCoefficients A U α.hom c) := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [relativeCoefficients_left]
  let x := ((α.pullback j.left).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest T.left))
    (LocallyConstant.const T.left c)).val
  have hx : x.left ≫ pullback.fst (A.pullback U.hom).scheme.hom j.left =
      (α.hom.app (.op ((Over.map j.left).obj (ConstantSectionsOn.ConstantSections.baseTest T.left)))
        (LocallyConstant.const T.left c)).val.left :=
    congrArg Over.Hom.left (α.pullback_basis j.left (ConstantSectionsOn.ConstantSections.baseTest T.left) (LocallyConstant.const T.left c))
  have hcomp := A.pullbackCompIso_inv_left_fst U.hom j.left
  have hcongr := pullbackCongrIso_hom_left_fst A (j.left ≫ U.hom) T.hom j.w
  have hn := IndependentFrames.LevelCover.relativeCoefficients_natural A U T j α.hom c
  have hright : (A.torsionPullback N j (IndependentFrames.LevelCover.relativeCoefficients A U α.hom c)).val.left =
      (α.hom.app (.op (Over.mk j.left)) (LocallyConstant.const T.left c)).val.left ≫
        pullback.fst A.scheme.hom U.hom :=
    (congrArg (fun x : A.torsionPoints N T => x.val.left) hn).trans
      (IndependentFrames.LevelCover.relativePointEquiv_left A U T j _)
  change ((x.left ≫ (A.pullbackCompIso U.hom j.left).inv.left) ≫
      (A.pullbackCongrIso (j.left ≫ U.hom) T.hom j.w).hom.left) ≫
      pullback.fst A.scheme.hom T.hom = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (x.left ≫ (A.pullbackCompIso U.hom j.left).inv.left) ≫ z) hcongr).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => x.left ≫ z) hcomp).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ pullback.fst A.scheme.hom U.hom) hx).trans
              ((congrArg (fun z => z ≫ pullback.fst A.scheme.hom U.hom)
                (level_mappedIdentity_left (A.pullback U.hom) α j.left c)).trans hright.symm))))))

/-- The unique classifying map for a full level respects the actual
geometric restriction operation, including its pullback comparisons. -/
theorem frameOfRelativeLevel_restrict [NeZero N] {T U : Over S} (j : T ⟶ U)
    (α : (A.pullback U.hom).FullLevel N) :
    IndependentFrames.LevelCover.frameOfRelativeLevel A T (α.restrict j) = j ≫ IndependentFrames.LevelCover.frameOfRelativeLevel A U α := by
  apply (IndependentFrames.LevelCover.independentFramePointsEquiv A T).injective
  apply Subtype.ext
  apply MonoidHom.ext
  intro c
  have hT := IndependentFrames.LevelCover.frameOfRelativeMap_coefficients A T (α.restrict j).hom
    (fun V => ((α.restrict j).app (.op V)).groupIsoToMulEquiv.injective)
  have hU := IndependentFrames.LevelCover.frameOfRelativeMap_coefficients A U α.hom
    (fun V => (α.app (.op V)).groupIsoToMulEquiv.injective)
  change Labels.LevelCover.frameTorsionHom A T (IndependentFrames.LevelCover.frameOfRelativeLevel A T (α.restrict j)) c =
    Labels.LevelCover.frameTorsionHom A T (j ≫ IndependentFrames.LevelCover.frameOfRelativeLevel A U α) c
  exact (congrArg (fun h : Labels.LevelCover.Coefficients g N →* A.torsionPoints N T => h c) hT).trans
    ((relativeCoefficients_restrict A j α c).trans
      ((congrArg (A.torsionPullback N j)
        (congrArg (fun h : Labels.LevelCover.Coefficients g N →* A.torsionPoints N U => h c) hU).symm).trans
        (Labels.LevelCover.frameTorsionHom_natural A j (IndependentFrames.LevelCover.frameOfRelativeLevel A U α) c)))

theorem frameOfRelativeLevel_injective [NeZero N] (T : Over S) :
    Function.Injective (IndependentFrames.LevelCover.frameOfRelativeLevel (N := N) A T) := by
  intro α β h
  apply (IndependentFrames.LevelCover.fullLevelFrameIsoEquiv A T).injective
  exact Subtype.ext h

/-- The full-level family functor with HilbertConstruction's geometric restriction maps
is defined without a chosen level on the original abelian scheme. The
functor laws follow from the actual classifying frame maps. -/
def fullLevelFamilyFunctor [NeZero N] : (Over S)ᵒᵖ ⥤ Type 1 where
  obj T := (A.pullback T.unop.hom).FullLevel N
  map f := TypeCat.ofHom (fun α => α.restrict f.unop)
  map_id T := by
    ext α
    apply frameOfRelativeLevel_injective A T.unop
    exact (frameOfRelativeLevel_restrict A (𝟙 T.unop) α).trans (Category.id_comp _)
  map_comp {T U V} f h := by
    ext α
    apply frameOfRelativeLevel_injective A V.unop
    exact (frameOfRelativeLevel_restrict A (h.unop ≫ f.unop) α).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => h.unop ≫ q) (frameOfRelativeLevel_restrict A f.unop α).symm).trans
          (frameOfRelativeLevel_restrict A h.unop (α.restrict f.unop)).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.FrameRestriction.LevelCover
