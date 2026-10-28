import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.BaseChange

/-! # Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Transport embedded flat families through specified Cartesian ambient squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {P : Over S} {Q : Over T}

/-- The inverse-image ideal is the closed subscheme in the Cartesian ambient square. -/
theorem ClosedFamily.Transport.closedFamilyTransport_isPullback (p : Q.left ⟶ P.left) (f : T ⟶ S)
    (h : IsPullback p Q.hom P.hom f) (I : P.left.IdealSheafData) :
    IsPullback ((I.comapIso p).hom ≫ pullback.snd p I.subschemeι)
      ((I.comap p).subschemeι ≫ Q.hom) (I.subschemeι ≫ P.hom) f := by
  have hs : IsPullback (I.comap p).subschemeι
      ((I.comapIso p).hom ≫ pullback.snd p I.subschemeι) p I.subschemeι := by
    apply isPullback_of_isClosedImmersion
    · calc
        (I.comap p).subschemeι ≫ p = ((I.comapIso p).hom ≫ pullback.fst p I.subschemeι) ≫ p :=
          congrArg (fun a => a ≫ p) (I.comapIso_hom_fst p).symm
        _ = _ := by rw [Category.assoc, pullback.condition, ← Category.assoc]
    · rw [I.ker_subschemeι, (I.comap p).ker_subschemeι]
  exact hs.flip.paste_vert h

@[ext]
theorem Closed.Families.FlatClosedFamily.ext {F G : Closed.Families.FlatClosedFamily P} (h : F.ideal = G.ideal) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Base change through any chosen Cartesian ambient square. -/
def Closed.Families.FlatClosedFamily.pullbackAlong (F : Closed.Families.FlatClosedFamily P) (p : Q.left ⟶ P.left) (f : T ⟶ S)
    (h : IsPullback p Q.hom P.hom f) : Closed.Families.FlatClosedFamily Q where
  ideal := F.ideal.comap p
  flat := MorphismProperty.of_isPullback (P := @Flat)
    (ClosedFamily.Transport.closedFamilyTransport_isPullback p f h F.ideal) F.flat
  locallyFinitePresentation := MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (ClosedFamily.Transport.closedFamilyTransport_isPullback p f h F.ideal) F.locallyFinitePresentation

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
