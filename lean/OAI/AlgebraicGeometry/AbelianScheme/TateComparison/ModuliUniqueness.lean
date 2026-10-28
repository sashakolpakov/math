import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

/-! # Moduli Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Full PEL-family isomorphisms determine the classifying map, both on
the integral model and on its actual generic fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

section

universe u
variable {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]
  {s N : ℕ} {B : Scheme.{u}} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}

theorem PELModuli.PELModuliCandidate.classifyingMap_eq_of_familyIso (M : PELModuli.PELModuliCandidate P N B)
    (base : NumberField.RingOfIntegers E →+* Γ(B, ⊤)) (h : M.ClassifiesReduced base)
    {T : Over B} [IsReduced T.left] (x y : T ⟶ M.space)
    (e : PELModuli.PELFamilyIso (M.family.pullback x.left) (M.family.pullback y.left)) : x = y := by
  obtain ⟨z, _, hz⟩ := h.2 T (M.family.pullback y.left) (h.1 T y)
  exact (hz x ⟨e⟩).trans (hz y ⟨PELModuli.PELFamilyIso.refl _⟩).symm

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)

include h in
theorem Data.SphericalPELAlbaneseData.genericMap_eq_of_familyIso {T : Over (Spec (.of K))} [IsReduced T.left]
    (x y : T ⟶ D.space)
    (e : PELModuli.PELFamilyIso (D.family.pullback x.left) (D.family.pullback y.left)) : x = y := by
  let a := ((Over.mapPullbackAdj D.generic).homEquiv T D.model.space).symm
  have : IsReduced ((Over.map D.generic).obj T).left := inferInstanceAs (IsReduced T.left)
  apply a.injective
  let ex := D.model.family.pullbackComp (pullback.fst D.model.space.hom D.generic) x.left
  let ey := D.model.family.pullbackComp (pullback.fst D.model.space.hom D.generic) y.left
  exact D.model.classifyingMap_eq_of_familyIso D.baseAction h.classifies (a x) (a y)
    (ex.symm.trans (e.trans ey))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
