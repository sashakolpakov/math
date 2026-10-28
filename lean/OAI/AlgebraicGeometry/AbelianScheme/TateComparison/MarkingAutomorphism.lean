import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ModuliMarkingMaps
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

/-! # Marking Automorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! Scalar marking changes give actual automorphisms of the integral
PEL moduli model and of its number-field generic fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)

def Data.SphericalPELAlbaneseData.modelMarkingAutomorphism (a : (ZMod D.level)ˣ) : D.model.space ≅ D.model.space := by
  have : IsReduced D.model.space.left := h.reduced
  exact D.model.scalarMarkingIso D.baseAction h.classifies a

def Data.SphericalPELAlbaneseData.markingAutomorphism (a : (ZMod D.level)ˣ) : D.space ≅ D.space :=
  (Over.pullback D.generic).mapIso (D.modelMarkingAutomorphism h a)

def Data.SphericalPELAlbaneseData.qMarkingAutomorphism (hq : Nat.Coprime q D.level) : D.space ≅ D.space :=
  D.markingAutomorphism h (ZMod.unitOfCoprime q hq)

theorem Data.SphericalPELAlbaneseData.modelMarkingAutomorphism_family (a : (ZMod D.level)ˣ) :
    Nonempty (PELModuli.PELFamilyIso (D.model.family.pullback (D.modelMarkingAutomorphism h a).hom.left)
      ((D.model.family.pullback (𝟙 D.model.space.left)).shiftMarking a)) := by
  have : IsReduced D.model.space.left := h.reduced
  exact D.model.scalarMarkingMap_classifies D.baseAction h.classifies a

end

/-! Pulling the universal family along the constructed marking
automorphism is isomorphic to its actual scalar marking change, over
the number-field generic fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)

def Data.SphericalPELAlbaneseData.markingFamilyIso (a : (ZMod D.level)ˣ) :
    PELModuli.PELFamilyIso (D.family.pullback (D.markingAutomorphism h a).hom.left) (D.family.shiftMarking a) := by
  have : IsReduced D.model.space.left := h.reduced
  let p := CategoryTheory.Limits.pullback.fst D.model.space.hom D.generic
  let u := (D.modelMarkingAutomorphism h a).hom.left
  let v := (D.markingAutomorphism h a).hom.left
  have hsquare : v ≫ p = p ≫ u :=
    AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (D.modelMarkingAutomorphism h a).hom D.generic
  let e₀ := D.model.family.pullbackComp p v
  let e₁ := PELModuli.PELFamilyIso.fromEquality (congrArg (fun z => D.model.family.pullback z) hsquare)
  let e₂ := (D.model.family.pullbackComp u p).symm
  let e₃ := (D.model.scalarMarkingFamilyIso D.baseAction h.classifies a).pullback p
  let e₄ := D.model.markingSourceFamily.shiftMarkingPullbackIso a p
  let e₅ := (D.model.family.pullbackFactor p (𝟙 D.model.space.left) p
    (Category.comp_id p)).symm.shiftMarking a
  exact e₀.trans (e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅))))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
