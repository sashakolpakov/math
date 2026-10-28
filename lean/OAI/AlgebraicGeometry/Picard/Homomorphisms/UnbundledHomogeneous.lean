import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Unbundled Homogeneous -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard

noncomputable section

/-! Homogeneous Picard classes for a group scheme, without a fixed
relative-dimension parameter. The definitions agree with the existing
abelian-scheme API whenever a dimension is specified. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}}

/-- Translation by a test-scheme point, with the test-scheme coordinate fixed. -/
def translation (A : Over S) [GrpObj A] {T : Over S} (a : T ⟶ A) :
    T ⊗ A ⟶ T ⊗ A :=
  lift (fst T A) ((fst T A ≫ a) * snd T A)

@[simp]
theorem translation_fst (A : Over S) [GrpObj A] {T : Over S} (a : T ⟶ A) :
    (translation A) a ≫ fst T A = fst T A := by
  simp [translation]

@[simp]
theorem translation_snd (A : Over S) [GrpObj A] {T : Over S} (a : T ⟶ A) :
    (translation A) a ≫ snd T A = (fst T A ≫ a) * snd T A := by
  simp [translation]

@[simp]
theorem translation_one (A : Over S) [GrpObj A] (T : Over S) :
    (translation A) (1 : T ⟶ A) = 𝟙 (T ⊗ A) := by
  simp [translation]

/-- A line-bundle class is homogeneous if every translate of each of its
base changes has the same relative Picard class. -/
def IsHomogeneousPicardClass (A : Over S) [GrpObj A] (T : Over S)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (.op T)) : Prop :=
  ∀ (U : Over S) (f : U ⟶ T) (a : U ⟶ A),
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((translation A) a).left
          ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op q)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U)
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op q)

theorem IsHomogeneousPicardClass.pullback (A : Over S) [GrpObj A]
    {T U : Over S} {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (.op T)}
    (hq : (IsHomogeneousPicardClass A) T q) (f : U ⟶ T) :
    (IsHomogeneousPicardClass A) U ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op q) := by
  intro V h a
  simpa only [op_comp, Functor.map_comp_apply] using hq V (h ≫ f) a

/-- Trivial line bundles give homogeneous relative Picard classes. -/
theorem trivialClass_homogeneous (A : Over S) [GrpObj A] (T : Over S) :
    (IsHomogeneousPicardClass A) T
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).obj T)) := by
  intro U f a
  apply congrArg (fun q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (.op U) =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U) q)
  have h := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).map f)
  exact (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((translation A) a).left) h).trans
    ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial ((translation A) a).left).trans h.symm)

/-- The presheaf of homogeneous line-bundle classes. -/
def homogeneousPicardPresheaf (A : Over S) [GrpObj A] :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj T //
    (IsHomogeneousPicardClass A) T.unop q}
  map f := TypeCat.ofHom fun q =>
    ⟨(AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f q.val, q.property.pullback A f.unop⟩
  map_id T := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map_id_apply T q.val
  map_comp f h := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map_comp_apply f h q.val

/-- Forget the homogeneity condition. -/
def homogeneousPicardInclusion (A : Over S) [GrpObj A] :
    (homogeneousPicardPresheaf A) ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A where
  app _ := TypeCat.ofHom Subtype.val
  naturality {T U} f := by
    apply ConcreteCategory.ext_apply
    intro q
    rfl

/-- The fppf sheaf of homogeneous line-bundle classes. -/
def homogeneousPicardSheaf (A : Over S) [GrpObj A] :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (homogeneousPicardPresheaf A)

/-- The identity section of the homogeneous Picard sheaf. -/
def trivialHomogeneousPicardClass (A : Over S) [GrpObj A] (T : Over S) :
    (UnbundledPicard.homogeneousPicardSheaf A).obj.obj (.op T) :=
  (toSheafify (Scheme.fppfTopology.over S) (homogeneousPicardPresheaf A)).app (.op T)
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A).obj T),
      (trivialClass_homogeneous A) T⟩

/-- The homogeneous Picard sheaf maps canonically to the full Picard sheaf. -/
def homogeneousPicardSheafInclusion (A : Over S) [GrpObj A] :
    (UnbundledPicard.homogeneousPicardSheaf A) ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (homogeneousPicardInclusion A)

theorem homogeneousPicardSheaf_eq_bundled {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    UnbundledPicard.homogeneousPicardSheaf A.scheme = A.homogeneousPicardSheaf := rfl

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard
