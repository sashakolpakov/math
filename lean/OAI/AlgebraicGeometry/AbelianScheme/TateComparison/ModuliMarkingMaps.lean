import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction

/-! # Moduli Marking Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The fine moduli classification constructs the scalar marking map
on the actual reduced moduli scheme, together with its PEL-family
isomorphism. No marking automorphism is supplied as extra data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

section

def PELModuli.PELFamilyIso.fromEquality {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
    {D E : PEL.PELFamilyData R g N S} (h : D = E) : PELModuli.PELFamilyIso D E := by
  subst E
  exact PELModuli.PELFamilyIso.refl D

end

variable {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]
  {s N : ℕ} {B : Scheme.{u}} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  (M : PELModuli.PELModuliCandidate P N B) (base : NumberField.RingOfIntegers E →+* Γ(B, ⊤))
  (h : M.ClassifiesReduced base) [IsReduced M.space.left]

def PELModuli.PELModuliCandidate.markingSourceFamily : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N M.space.left :=
  M.family.pullback (𝟙 M.space.left)

include h in
theorem PELModuli.PELModuliCandidate.markingSourceFamily_isPEL :
    PELModuli.IsPELFamily P (M.space.hom.appTop.hom.comp base) M.markingSourceFamily :=
  h.1 M.space (𝟙 M.space)

def PELModuli.PELModuliCandidate.scalarMarkingMap (a : (ZMod N)ˣ) : M.space ⟶ M.space :=
  (h.2 M.space (M.markingSourceFamily.shiftMarking a)
    ((MarkingAction.shiftMarking_isPELFamily P _ _ a).mpr (M.markingSourceFamily_isPEL base h))).choose

theorem PELModuli.PELModuliCandidate.scalarMarkingMap_classifies (a : (ZMod N)ˣ) :
    Nonempty (PELModuli.PELFamilyIso (M.family.pullback (M.scalarMarkingMap base h a).left)
      (M.markingSourceFamily.shiftMarking a)) :=
  (h.2 M.space (M.markingSourceFamily.shiftMarking a)
    ((MarkingAction.shiftMarking_isPELFamily P _ _ a).mpr (M.markingSourceFamily_isPEL base h))).choose_spec.1

def PELModuli.PELModuliCandidate.scalarMarkingFamilyIso (a : (ZMod N)ˣ) :
    PELModuli.PELFamilyIso (M.family.pullback (M.scalarMarkingMap base h a).left)
      (M.markingSourceFamily.shiftMarking a) :=
  (M.scalarMarkingMap_classifies base h a).some

include h in
theorem PELModuli.PELModuliCandidate.scalarMarkingMap_unique (a : (ZMod N)ˣ) (x : M.space ⟶ M.space)
    (hx : Nonempty (PELModuli.PELFamilyIso (M.family.pullback x.left) (M.markingSourceFamily.shiftMarking a))) :
    x = M.scalarMarkingMap base h a :=
  (h.2 M.space (M.markingSourceFamily.shiftMarking a)
    ((MarkingAction.shiftMarking_isPELFamily P _ _ a).mpr (M.markingSourceFamily_isPEL base h))).choose_spec.2 x hx

theorem PELModuli.PELModuliCandidate.scalarMarkingMap_one : M.scalarMarkingMap base h 1 = 𝟙 M.space := by
  apply Eq.symm
  apply M.scalarMarkingMap_unique base h
  exact ⟨PELModuli.PELFamilyIso.fromEquality M.markingSourceFamily.shiftMarking_one.symm⟩

def PELModuli.PELModuliCandidate.scalarMarkingCompositeIso (a b : (ZMod N)ˣ) :
    PELModuli.PELFamilyIso (M.family.pullback (M.scalarMarkingMap base h a ≫ M.scalarMarkingMap base h b).left)
      (M.markingSourceFamily.shiftMarking (b * a)) := by
  let xa := M.scalarMarkingMap base h a
  let xb := M.scalarMarkingMap base h b
  let e₀ := (M.family.pullbackComp xb.left xa.left).symm
  let e₁ := (M.scalarMarkingFamilyIso base h b).pullback xa.left
  let e₂ := M.markingSourceFamily.shiftMarkingPullbackIso b xa.left
  let e₃ := (M.family.pullbackFactor xa.left (𝟙 M.space.left) xa.left
    (Category.comp_id xa.left)).symm.shiftMarking b
  let e₄ := (M.scalarMarkingFamilyIso base h a).shiftMarking b
  let e₅ := PELModuli.PELFamilyIso.fromEquality (M.markingSourceFamily.shiftMarking_mul a b)
  exact e₀.trans (e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅))))

theorem PELModuli.PELModuliCandidate.scalarMarkingMap_mul (a b : (ZMod N)ˣ) :
    M.scalarMarkingMap base h a ≫ M.scalarMarkingMap base h b = M.scalarMarkingMap base h (b * a) :=
  M.scalarMarkingMap_unique base h (b * a) _ ⟨M.scalarMarkingCompositeIso base h a b⟩

def PELModuli.PELModuliCandidate.scalarMarkingIso (a : (ZMod N)ˣ) : M.space ≅ M.space where
  hom := M.scalarMarkingMap base h a
  inv := M.scalarMarkingMap base h a⁻¹
  hom_inv_id := by rw [PELModuli.PELModuliCandidate.scalarMarkingMap_mul, inv_mul_cancel, PELModuli.PELModuliCandidate.scalarMarkingMap_one]
  inv_hom_id := by rw [PELModuli.PELModuliCandidate.scalarMarkingMap_mul, mul_inv_cancel, PELModuli.PELModuliCandidate.scalarMarkingMap_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
