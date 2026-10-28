import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAutomorphism

/-! # Marking Finite Order -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual marking automorphism has finite order because scalar
level markings form the finite unit group modulo the level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def Data.SphericalPELAlbaneseData.markingEndHom : (ZMod D.level)ˣ →* End D.space where
  toFun a := End.of (D.markingAutomorphism hg a).hom
  map_one' := by
    have : IsReduced D.model.space.left := hg.reduced
    change (Over.pullback D.generic).map (D.model.scalarMarkingMap D.baseAction hg.classifies 1) = 𝟙 D.space
    rw [PELModuli.PELModuliCandidate.scalarMarkingMap_one]
    exact (Over.pullback D.generic).map_id _
  map_mul' a b := by
    have : IsReduced D.model.space.left := hg.reduced
    change (Over.pullback D.generic).map (D.model.scalarMarkingMap D.baseAction hg.classifies (a * b)) =
      (Over.pullback D.generic).map (D.model.scalarMarkingMap D.baseAction hg.classifies b) ≫
        (Over.pullback D.generic).map (D.model.scalarMarkingMap D.baseAction hg.classifies a)
    rw [← Functor.map_comp, PELModuli.PELModuliCandidate.scalarMarkingMap_mul]

theorem Data.SphericalPELAlbaneseData.markingAutomorphism_finiteOrder (a : (ZMod D.level)ˣ) :
    ∃ n : ℕ, 0 < n ∧ (End.of (D.markingAutomorphism hg a).hom) ^ n = 1 := by
  have : NeZero D.level := ⟨by have := hg.fullLevel; omega⟩
  refine ⟨orderOf a, orderOf_pos a, ?_⟩
  change D.markingEndHom hg a ^ orderOf a = 1
  rw [← map_pow, pow_orderOf_eq_one, map_one]

theorem Data.SphericalPELAlbaneseData.qMarkingAutomorphism_finiteOrder (hq : Nat.Coprime q D.level) :
    ∃ n : ℕ, 0 < n ∧ (End.of (D.qMarkingAutomorphism hg hq).hom) ^ n = 1 :=
  D.markingAutomorphism_finiteOrder hg (ZMod.unitOfCoprime q hq)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
