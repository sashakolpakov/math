import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedIsomorphisms

/-! # Pullback Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-! Identity base change of embedded polarized objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P : Over S)

theorem PullbackIdentity.embeddedFamilyAmbientMap_id (T : Over S) : FamilyFunctor.embeddedFamilyAmbientMap P (𝟙 T) = 𝟙 _ :=
  congrArg Over.Hom.left prod.map_id_id

theorem PullbackIdentity.embeddedFamilyAmbientMap_comp {T U V : Over S} (f : T ⟶ U) (h : U ⟶ V) :
    FamilyFunctor.embeddedFamilyAmbientMap P (f ≫ h) = FamilyFunctor.embeddedFamilyAmbientMap P f ≫ FamilyFunctor.embeddedFamilyAmbientMap P h :=
  congrArg Over.Hom.left (by
    simpa only [Category.id_comp] using (prod.map_map f (𝟙 P) h (𝟙 P)).symm)

variable {P} {g N : ℕ} {δ : Fin g → ℕ} {T : Over S}

/-- The canonical identity comparison also preserves the ambient embedding. -/
def PolarizedIsomorphisms.EmbeddedLevelIso.pullbackId (A : PolarizedObjects.EmbeddedPolarizedObject P g δ N T) :
    PolarizedIsomorphisms.EmbeddedLevelIso (A.pullback (𝟙 T)) A where
  iso := Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.object
  embedding := by
    apply Over.OverMorphism.ext
    have hw := (A.pullback_embedding_isPullback (𝟙 T)).w
    have hi := A.object.abelian.pullbackIdIso_hom_left
    change A.object.abelian.pullbackIdIso.hom.left ≫ A.embedding.left =
      (A.pullback (𝟙 T)).embedding.left
    exact (congrArg (fun q => q ≫ A.embedding.left) hi).trans
      (hw.symm.trans (by rw [PullbackIdentity.embeddedFamilyAmbientMap_id, Category.comp_id]))

/-- Pullback is well-defined on isomorphism classes of embedded objects. -/
def PolarizedIsomorphisms.EmbeddedPolarizedClasses.pullback {U : Over S} (f : T ⟶ U)
    (q : PolarizedIsomorphisms.EmbeddedPolarizedClasses P g δ N U) : PolarizedIsomorphisms.EmbeddedPolarizedClasses P g δ N T :=
  Quotient.liftOn q (fun A => Quotient.mk _ (A.pullback f))
    (fun _ _ ⟨e⟩ => Quotient.sound ⟨e.pullback f⟩)

theorem PolarizedIsomorphisms.EmbeddedPolarizedClasses.pullback_id (q : PolarizedIsomorphisms.EmbeddedPolarizedClasses P g δ N T) :
    q.pullback (𝟙 T) = q := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨PolarizedIsomorphisms.EmbeddedLevelIso.pullbackId A⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded
