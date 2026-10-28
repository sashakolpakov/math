import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

/-! # Picard -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Translation-invariant classes in the relative Picard sheaf of an abelian
scheme. Invariance is imposed in the relative Picard sheaf, so a line bundle
pulled back from the test base is not mistaken for nontrivial relative data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {g : ℕ} {S : Scheme.{u}}

/-- Translation by a test-scheme point, with the test-scheme coordinate fixed. -/
def Abelian.Schemes.AbelianScheme.translation (A : Abelian.Schemes.AbelianScheme g S) {T : Over S} (a : T ⟶ A.scheme) :
    T ⊗ A.scheme ⟶ T ⊗ A.scheme :=
  lift (fst T A.scheme) ((fst T A.scheme ≫ a) * snd T A.scheme)

@[simp]
theorem Abelian.Schemes.AbelianScheme.translation_fst (A : Abelian.Schemes.AbelianScheme g S) {T : Over S} (a : T ⟶ A.scheme) :
    A.translation a ≫ fst T A.scheme = fst T A.scheme := by
  simp [Abelian.Schemes.AbelianScheme.translation]

@[simp]
theorem Abelian.Schemes.AbelianScheme.translation_snd (A : Abelian.Schemes.AbelianScheme g S) {T : Over S} (a : T ⟶ A.scheme) :
    A.translation a ≫ snd T A.scheme = (fst T A.scheme ≫ a) * snd T A.scheme := by
  simp [Abelian.Schemes.AbelianScheme.translation]

@[simp]
theorem Abelian.Schemes.AbelianScheme.translation_one (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    A.translation (1 : T ⟶ A.scheme) = 𝟙 (T ⊗ A.scheme) := by
  simp [Abelian.Schemes.AbelianScheme.translation]

/-- A line-bundle class is homogeneous if every translate of each of its
base changes has the same relative Picard class. -/
def Abelian.Schemes.AbelianScheme.IsHomogeneousPicardClass (A : Abelian.Schemes.AbelianScheme g S) (T : Over S)
    (q : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T)) : Prop :=
  ∀ (U : Over S) (f : U ⟶ T) (a : U ⟶ A.scheme),
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        (Line.Bundles.LineBundle.pullbackClass (A.translation a).left
          ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q)) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q)

theorem Abelian.Schemes.AbelianScheme.IsHomogeneousPicardClass.pullback (A : Abelian.Schemes.AbelianScheme g S)
    {T U : Over S} {q : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T)}
    (hq : A.IsHomogeneousPicardClass T q) (f : U ⟶ T) :
    A.IsHomogeneousPicardClass U ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q) := by
  intro V h a
  simpa only [op_comp, Functor.map_comp_apply] using hq V (h ≫ f) a

/-- Trivial line bundles give homogeneous relative Picard classes. -/
theorem Abelian.Schemes.AbelianScheme.trivialClass_homogeneous (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    A.IsHomogeneousPicardClass T
      (Line.Bundles.LineBundle.trivialClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T)) := by
  intro U f a
  apply congrArg (fun q : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op U) =>
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) q)
  have h := Line.Bundles.LineBundle.pullbackClass_trivial ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f)
  exact (congrArg (Line.Bundles.LineBundle.pullbackClass (A.translation a).left) h).trans
    ((Line.Bundles.LineBundle.pullbackClass_trivial (A.translation a).left).trans h.symm)

/-- The presheaf of homogeneous line-bundle classes. -/
def Abelian.Schemes.AbelianScheme.homogeneousPicardPresheaf (A : Abelian.Schemes.AbelianScheme g S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := {q : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj T //
    A.IsHomogeneousPicardClass T.unop q}
  map f := TypeCat.ofHom fun q =>
    ⟨(Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f q.val, q.property.pullback A f.unop⟩
  map_id T := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_id_apply T q.val
  map_comp f h := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_comp_apply f h q.val

/-- Forget the homogeneity condition. -/
def Abelian.Schemes.AbelianScheme.homogeneousPicardInclusion (A : Abelian.Schemes.AbelianScheme g S) :
    A.homogeneousPicardPresheaf ⟶ Picard.PicardSheaf.relativePicardPresheaf A.scheme where
  app _ := TypeCat.ofHom Subtype.val
  naturality {T U} f := by
    apply ConcreteCategory.ext_apply
    intro q
    rfl

/-- The fppf sheaf of homogeneous line-bundle classes. -/
def Abelian.Schemes.AbelianScheme.homogeneousPicardSheaf (A : Abelian.Schemes.AbelianScheme g S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    A.homogeneousPicardPresheaf

/-- The identity section of the homogeneous Picard sheaf. -/
def Abelian.Schemes.AbelianScheme.trivialHomogeneousPicardClass (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    A.homogeneousPicardSheaf.obj.obj (.op T) :=
  (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T)
    ⟨Line.Bundles.LineBundle.trivialClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T),
      A.trivialClass_homogeneous T⟩

/-- The homogeneous Picard sheaf maps canonically to the full Picard sheaf. -/
def Abelian.Schemes.AbelianScheme.homogeneousPicardSheafInclusion (A : Abelian.Schemes.AbelianScheme g S) :
    A.homogeneousPicardSheaf ⟶ Picard.PicardSheaf.relativePicardSheaf A.scheme :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    A.homogeneousPicardInclusion

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
