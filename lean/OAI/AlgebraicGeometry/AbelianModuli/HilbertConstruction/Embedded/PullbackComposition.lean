import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PullbackIdentity

/-! # Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-! Composition base change for embedded polarized objects and their class presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P : Over S} {g N : ℕ} {δ : Fin g → ℕ} {T U V : Over S}

/-- Maps over the new base into a test ambient are determined by their maps to the old ambient. -/
theorem PullbackComposition.embeddedAmbient_hom_ext (f : T ⟶ U) {Z : Over T.left}
    (a b : Z ⟶ FamilyFunctor.embeddedFamilyAmbient P T)
    (h : a.left ≫ FamilyFunctor.embeddedFamilyAmbientMap P f = b.left ≫ FamilyFunctor.embeddedFamilyAmbientMap P f) : a = b := by
  apply Over.OverMorphism.ext
  exact (FamilyFunctor.embeddedFamilyAmbient_isPullback P f).hom_ext h (a.w.trans b.w.symm)

/-- The comparison of iterated and composite pullback preserves the embedding. -/
def PolarizedIsomorphisms.EmbeddedLevelIso.pullbackComp (A : PolarizedObjects.EmbeddedPolarizedObject P g δ N V)
    (f : U ⟶ V) (h : T ⟶ U) :
    PolarizedIsomorphisms.EmbeddedLevelIso ((A.pullback f).pullback h) (A.pullback (h ≫ f)) where
  iso := Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A.object f.left h.left
  embedding := by
    change (A.object.abelian.pullbackCompIso f.left h.left).inv ≫ (A.pullback (h ≫ f)).embedding =
      ((A.pullback f).pullback h).embedding
    apply PullbackComposition.embeddedAmbient_hom_ext (h ≫ f)
    let e := (A.object.abelian.pullbackCompIso f.left h.left).inv.left
    let q := pullback.fst A.object.abelian.scheme.hom (h.left ≫ f.left)
    let qf := pullback.fst A.object.abelian.scheme.hom f.left
    let qh := pullback.fst (A.object.abelian.pullback f.left).scheme.hom h.left
    have he : e ≫ q = qh ≫ qf := A.object.abelian.pullbackCompIso_inv_left_fst f.left h.left
    have h₀ := (A.pullback_embedding_isPullback (h ≫ f)).w
    have h₁ := (A.pullback_embedding_isPullback f).w
    have h₂ := ((A.pullback f).pullback_embedding_isPullback h).w
    have hstart : (e ≫ (A.pullback (h ≫ f)).embedding.left) ≫
        FamilyFunctor.embeddedFamilyAmbientMap P (h ≫ f) = (qh ≫ qf) ≫ A.embedding.left :=
      ((Category.assoc _ _ _).trans (congrArg (fun p => e ≫ p) h₀)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun p => p ≫ A.embedding.left) he))
    have hmiddle : (qh ≫ qf) ≫ A.embedding.left =
        (((A.pullback f).pullback h).embedding.left ≫ FamilyFunctor.embeddedFamilyAmbientMap P h) ≫
          FamilyFunctor.embeddedFamilyAmbientMap P f :=
      ((Category.assoc _ _ _).trans (congrArg (fun p => qh ≫ p) h₁.symm)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun p => p ≫ FamilyFunctor.embeddedFamilyAmbientMap P f) h₂.symm))
    have hend : (((A.pullback f).pullback h).embedding.left ≫ FamilyFunctor.embeddedFamilyAmbientMap P h) ≫
        FamilyFunctor.embeddedFamilyAmbientMap P f =
          ((A.pullback f).pullback h).embedding.left ≫ FamilyFunctor.embeddedFamilyAmbientMap P (h ≫ f) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun p => ((A.pullback f).pullback h).embedding.left ≫ p)
          (PullbackIdentity.embeddedFamilyAmbientMap_comp P h f).symm)
    exact hstart.trans (hmiddle.trans hend)

theorem PolarizedIsomorphisms.EmbeddedPolarizedClasses.pullback_comp (f : U ⟶ V) (h : T ⟶ U)
    (q : PolarizedIsomorphisms.EmbeddedPolarizedClasses P g δ N V) :
    q.pullback (h ≫ f) = (q.pullback f).pullback h := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨(PolarizedIsomorphisms.EmbeddedLevelIso.pullbackComp A f h).symm⟩

/-- The embedded polarized full-level classes form a presheaf on test schemes. -/
def PullbackComposition.embeddedPolarizedFunctor (P : Over S) (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := PolarizedIsomorphisms.EmbeddedPolarizedClasses P g δ N T.unop
  map f := TypeCat.ofHom (PolarizedIsomorphisms.EmbeddedPolarizedClasses.pullback f.unop)
  map_id T := by
    ext q
    exact PolarizedIsomorphisms.EmbeddedPolarizedClasses.pullback_id q
  map_comp f h := by
    ext q
    exact PolarizedIsomorphisms.EmbeddedPolarizedClasses.pullback_comp f.unop h.unop q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded
