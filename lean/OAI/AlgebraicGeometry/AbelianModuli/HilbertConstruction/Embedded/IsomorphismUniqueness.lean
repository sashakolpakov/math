import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedIsomorphisms

/-! # Isomorphism Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
The dual component of a polarized isomorphism is determined by its abelian
component. A fixed closed embedding therefore makes embedded isomorphisms
unique. This is not the rigidity theorem for level structure alone.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}

/-- A polarized isomorphism is determined by its map on the abelian scheme. -/
theorem Moduli.Isomorphisms.LevelPreservingIso.ext_abelian {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e h : Moduli.Isomorphisms.LevelPreservingIso A B) (he : e.abelian.hom = h.abelian.hom) : e = h := by
  have : Epi ((Over.forget S).map A.polarization.isogeny.hom) :=
    Flat.epi_of_flat_of_surjective A.polarization.isogeny.hom.left
  have : Epi A.polarization.isogeny.hom := Functor.epi_of_epi_map (Over.forget S) inferInstance
  have hd : e.dual.hom = h.dual.hom := (cancel_epi A.polarization.isogeny.hom).mp
    (e.polarization.trans ((congrArg (fun a => a ≫ B.polarization.isogeny.hom) he).trans
      h.polarization.symm))
  have hab : e.abelian = h.abelian := Iso.ext he
  have hdual : e.dual = h.dual := Iso.ext hd
  cases e
  cases h
  cases hab
  cases hdual
  rfl

variable {P : Over S} {T : Over S}

/-- Two isomorphisms preserving the same fixed closed embeddings coincide. -/
instance Embedded.IsomorphismUniqueness.embeddedLevelIso_subsingleton (A B : Embedded.PolarizedObjects.EmbeddedPolarizedObject P g δ N T) :
    Subsingleton (Embedded.PolarizedIsomorphisms.EmbeddedLevelIso A B) where
  allEq e h := by
    have : Mono ((Over.forget T.left).map B.embedding) :=
      inferInstanceAs (Mono B.embedding.left)
    have : Mono B.embedding := Functor.mono_of_mono_map (Over.forget T.left) inferInstance
    have hab : e.iso.abelian.hom = h.iso.abelian.hom :=
      (cancel_mono B.embedding).mp (e.embedding.trans h.embedding.symm)
    have hi := Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e.iso h.iso hab
    cases e
    cases h
    cases hi
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
