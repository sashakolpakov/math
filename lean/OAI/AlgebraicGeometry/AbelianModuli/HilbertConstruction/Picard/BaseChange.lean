import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseChange

noncomputable section

/-!
The relative Picard sheaf commutes with arbitrary base change. The proof uses
the canonical fiber-product isomorphism and the compatibility of
sheafification with restriction to a slice site.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S S' : Scheme.{u}}

/-- Two descriptions of the total family over a test scheme over `S'`. -/
def familyBaseChangeIso (X : Over S) (f : S' ⟶ S) (T : Over S') :
    pullback T.hom (pullback.snd X.hom f) ≅ pullback (T.hom ≫ f) X.hom :=
  pullbackSymmetry T.hom (pullback.snd X.hom f) ≪≫
    pullbackLeftPullbackSndIso X.hom f T.hom ≪≫
      pullbackSymmetry X.hom (T.hom ≫ f)

@[reassoc (attr := simp)]
theorem familyBaseChangeIso_hom_fst (X : Over S) (f : S' ⟶ S) (T : Over S') :
    (familyBaseChangeIso X f T).hom ≫ pullback.fst (T.hom ≫ f) X.hom =
      pullback.fst T.hom (pullback.snd X.hom f) := by
  simp [familyBaseChangeIso]

@[reassoc (attr := simp)]
theorem familyBaseChangeIso_hom_snd (X : Over S) (f : S' ⟶ S) (T : Over S') :
    (familyBaseChangeIso X f T).hom ≫ pullback.snd (T.hom ≫ f) X.hom =
      pullback.snd T.hom (pullback.snd X.hom f) ≫ pullback.fst X.hom f := by
  simp [familyBaseChangeIso]

/-- The fiber-product identification is natural in the test scheme. -/
def familyBaseChangeNatIso (X : Over S) (f : S' ⟶ S) :
    PicardSheaf.familySchemeFunctor ((Over.pullback f).obj X) ≅
      Over.map f ⋙ PicardSheaf.familySchemeFunctor X :=
  NatIso.ofComponents (familyBaseChangeIso X f) (by
    intro T U a
    apply pullback.hom_ext
    · change ((a ▷ (Over.pullback f).obj X).left ≫ (familyBaseChangeIso X f U).hom) ≫
        pullback.fst (U.hom ≫ f) X.hom =
        ((familyBaseChangeIso X f T).hom ≫ ((Over.map f).map a ▷ X).left) ≫
          pullback.fst (U.hom ≫ f) X.hom
      simp only [Over.whiskerRight_left, Category.assoc, familyBaseChangeIso_hom_fst,
        pullback.map, pullback.lift_fst, familyBaseChangeIso_hom_fst_assoc,
        Over.pullback_obj_hom, Over.map_obj_hom, Over.map_map_left]
    · change ((a ▷ (Over.pullback f).obj X).left ≫ (familyBaseChangeIso X f U).hom) ≫
        pullback.snd (U.hom ≫ f) X.hom =
        ((familyBaseChangeIso X f T).hom ≫ ((Over.map f).map a ▷ X).left) ≫
          pullback.snd (U.hom ≫ f) X.hom
      simp only [Over.whiskerRight_left, Category.assoc, familyBaseChangeIso_hom_snd,
        pullback.map, pullback.lift_snd, Category.comp_id, pullback.lift_snd_assoc,
        Over.pullback_obj_hom, Over.map_obj_hom])

/-- Line-bundle classes on the changed family form the restricted presheaf. -/
def relativePicardPresheafBaseChangeIso (X : Over S) (f : S' ⟶ S) :
    PicardSheaf.relativePicardPresheaf ((Over.pullback f).obj X) ≅
      (Over.map f).op ⋙ PicardSheaf.relativePicardPresheaf X :=
  Functor.isoWhiskerRight (NatIso.op (familyBaseChangeNatIso X f)).symm
    Line.Bundles.lineBundleClassFunctor

/-- The fppf Picard sheaf is compatible with arbitrary change of base. -/
def relativePicardSheafBaseChangeIso (X : Over S) (f : S' ⟶ S) :
    PicardSheaf.relativePicardSheaf ((Over.pullback f).obj X) ≅
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).obj (PicardSheaf.relativePicardSheaf X) :=
  (presheafToSheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      (relativePicardPresheafBaseChangeIso X f) ≪≫
    ((Over.map f).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app
        (PicardSheaf.relativePicardPresheaf X)

@[simp]
theorem relativePicardPresheafBaseChangeIso_hom_app (X : Over S) (f : S' ⟶ S)
    (T : Over S') (q : (PicardSheaf.relativePicardPresheaf ((Over.pullback f).obj X)).obj (.op T)) :
    (relativePicardPresheafBaseChangeIso X f).hom.app (.op T) q =
      Line.Bundles.LineBundle.pullbackClass (familyBaseChangeIso X f T).inv q := rfl

@[simp]
theorem relativePicardPresheafBaseChangeIso_inv_app (X : Over S) (f : S' ⟶ S)
    (T : Over S') (q : (PicardSheaf.relativePicardPresheaf X).obj (.op ((Over.map f).obj T))) :
    (relativePicardPresheafBaseChangeIso X f).inv.app (.op T) q =
      Line.Bundles.LineBundle.pullbackClass (familyBaseChangeIso X f T).hom q := rfl

/-- The sheaf comparison agrees with the pullback comparison on actual
line-bundle classes, before sheafification. -/
theorem toRelativePicard_baseChange (X : Over S) (f : S' ⟶ S) :
    PicardSheaf.toRelativePicard ((Over.pullback f).obj X) ≫
        (relativePicardSheafBaseChangeIso X f).hom.hom =
      (relativePicardPresheafBaseChangeIso X f).hom ≫
        Functor.whiskerLeft (Over.map f).op (PicardSheaf.toRelativePicard X) := by
  change toSheafify (Scheme.fppfTopology.over S') _ ≫
      (sheafifyMap (Scheme.fppfTopology.over S')
          (relativePicardPresheafBaseChangeIso X f).hom ≫
        (((Over.map f).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
          (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).hom.app
            (PicardSheaf.relativePicardPresheaf X)).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    (Over.map f).toSheafify_pullbackSheafificationCompatibility]
  rfl

/-- Elementwise compatibility of the Picard sheaf comparison with line bundles. -/
theorem toRelativePicard_baseChange_apply (X : Over S) (f : S' ⟶ S) (T : Over S')
    (q : (PicardSheaf.relativePicardPresheaf ((Over.pullback f).obj X)).obj (.op T)) :
    (relativePicardSheafBaseChangeIso X f).hom.hom.app (.op T)
        ((PicardSheaf.toRelativePicard ((Over.pullback f).obj X)).app (.op T) q) =
      (PicardSheaf.toRelativePicard X).app (.op ((Over.map f).obj T))
        (Line.Bundles.LineBundle.pullbackClass (familyBaseChangeIso X f T).inv q) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (toRelativePicard_baseChange X f) (.op T)) q

/-- Base change carries the trivial relative Picard class to the trivial class. -/
theorem trivialPicardClass_baseChange (X : Over S) (f : S' ⟶ S) (T : Over S') :
    (relativePicardSheafBaseChangeIso X f).hom.hom.app (.op T)
        (PicardSheaf.trivialPicardClass ((Over.pullback f).obj X) T) =
      PicardSheaf.trivialPicardClass X ((Over.map f).obj T) := by
  exact (toRelativePicard_baseChange_apply X f T
    (Line.Bundles.LineBundle.trivialClass _)).trans
      (congrArg (fun q : (PicardSheaf.relativePicardPresheaf X).obj (.op ((Over.map f).obj T)) =>
        (PicardSheaf.toRelativePicard X).app (.op ((Over.map f).obj T)) q)
        (Line.Bundles.LineBundle.pullbackClass_trivial (familyBaseChangeIso X f T).inv))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseChange
