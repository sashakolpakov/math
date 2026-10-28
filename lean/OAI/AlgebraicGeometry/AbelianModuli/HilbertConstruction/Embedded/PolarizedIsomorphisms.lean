import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedFamilyMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Functor

/-! # Polarized Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedIsomorphisms

noncomputable section

/-! Isomorphism classes of embedded polarized objects and their concrete forgetful maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P : Over S} {g N : ℕ} {δ : Fin g → ℕ} {T U : Over S}

/-- An isomorphism preserves the full polarized object and its ambient embedding. -/
structure EmbeddedLevelIso (A B : PolarizedObjects.EmbeddedPolarizedObject P g δ N T) where
  iso : Moduli.Isomorphisms.LevelPreservingIso A.object B.object
  embedding : iso.abelian.hom ≫ B.embedding = A.embedding

namespace EmbeddedLevelIso

variable {A B C : PolarizedObjects.EmbeddedPolarizedObject P g δ N T}

def refl (A : PolarizedObjects.EmbeddedPolarizedObject P g δ N T) : EmbeddedLevelIso A A :=
  ⟨Moduli.Isomorphisms.LevelPreservingIso.refl A.object, Category.id_comp _⟩

def symm (e : EmbeddedLevelIso A B) : EmbeddedLevelIso B A where
  iso := e.iso.symm
  embedding := by
    change e.iso.abelian.inv ≫ A.embedding = B.embedding
    exact (congrArg (fun i => e.iso.abelian.inv ≫ i) e.embedding.symm).trans
      (by simp only [Iso.inv_hom_id_assoc])

def trans (e : EmbeddedLevelIso A B) (h : EmbeddedLevelIso B C) : EmbeddedLevelIso A C where
  iso := e.iso.trans h.iso
  embedding := (Category.assoc _ _ _).trans
    ((congrArg (fun i => e.iso.abelian.hom ≫ i) h.embedding).trans e.embedding)

/-- Embedded isomorphisms are preserved by base change. -/
def pullback (e : EmbeddedLevelIso A B) (f : U ⟶ T) :
    EmbeddedLevelIso (A.pullback f) (B.pullback f) where
  iso := e.iso.pullback f.left
  embedding := by
    let F := Over.pullback f.left
    let a := (PolarizedObjects.embeddedFamilyAmbientBaseChangeIso P f).hom
    change F.map e.iso.abelian.hom ≫ (F.map B.embedding ≫ a) = F.map A.embedding ≫ a
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun i => i ≫ a)
        ((F.map_comp e.iso.abelian.hom B.embedding).symm.trans (congrArg F.map e.embedding)))

/-- The underlying defining ideal is invariant under embedded isomorphisms. -/
theorem closedFamily_eq (e : EmbeddedLevelIso A B) : A.closedFamily = B.closedFamily := by
  have hi : IsIso e.iso.abelian.hom.left :=
    inferInstanceAs (IsIso ((Over.forget T.left).map e.iso.abelian.hom))
  apply Closed.Families.FlatClosedFamily.ext
  exact (congrArg (fun i => i.left.ker) e.embedding).symm.trans
    (Scheme.Hom.ker_comp_of_isIso e.iso.abelian.hom.left B.embedding.left)

end EmbeddedLevelIso

/-- Equivalence of embedded polarized objects. -/
def embeddedPolarizedSetoid (P : Over S) (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) (T : Over S) :
    Setoid (PolarizedObjects.EmbeddedPolarizedObject P g δ N T) where
  r A B := Nonempty (EmbeddedLevelIso A B)
  iseqv := ⟨fun A => ⟨EmbeddedLevelIso.refl A⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨h⟩ => ⟨e.trans h⟩⟩

def EmbeddedPolarizedClasses (P : Over S) (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) (T : Over S) :=
  Quotient (embeddedPolarizedSetoid P g δ N T)

/-- The ideal-sheaf family is independent of the representative of an embedded class. -/
def EmbeddedPolarizedClasses.closedFamily (q : EmbeddedPolarizedClasses P g δ N T) :
    Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T) :=
  Quotient.liftOn q PolarizedObjects.EmbeddedPolarizedObject.closedFamily (fun _ _ ⟨e⟩ => e.closedFamily_eq)

/-- Forgetting the embedding gives the original polarized full-level moduli class. -/
def EmbeddedPolarizedClasses.forget (q : EmbeddedPolarizedClasses P g δ N T) :
    Moduli.Isomorphisms.PolarizedLevelClasses g δ N T.left :=
  Quotient.liftOn q (fun A => PolarizationData.PolarizedAbelianWithFullLevel.classOf A.object)
    (fun _ _ ⟨e⟩ => Quotient.sound ⟨e.iso⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedIsomorphisms
