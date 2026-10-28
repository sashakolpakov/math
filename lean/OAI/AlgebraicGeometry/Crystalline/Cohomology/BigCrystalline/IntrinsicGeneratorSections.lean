import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSectionCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGeneratorCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGenerators

/-! # Intrinsic Generator Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections

noncomputable section

/-! # Actual native section coordinates from the unique big-site generators -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX

def representative (j : ℕ) (x : A₀ ⟶ (K).X j) (Q : Site.Object p k X) :=
  IntrinsicGenerators.BigCrystallineIntrinsicGenerators.representative p k B σ a j Q
    ((IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sourceSections p k B σ a j x).app (op ((ι).obj Q)) (1 : R))

theorem generator_representative (j : ℕ) (x : A₀ ⟶ (K).X j) (Q : Site.Object p k X) :
    (IntrinsicGenerators.BigCrystallineIntrinsicGenerators.generator p k B σ a j).app (op ((ι).obj Q))
        (representative p k B σ a j x Q) =
      (IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sourceSections p k B σ a j x).app (op ((ι).obj Q)) (1 : R) :=
  IntrinsicGenerators.BigCrystallineIntrinsicGenerators.generator_representative p k B σ a j Q
    ((IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sourceSections p k B σ a j x).app (op ((ι).obj Q)) (1 : R))

theorem representative_eq (j : ℕ) (x : A₀ ⟶ (K).X j) (Q : Site.Object p k X)
    (z : (IntrinsicGenerators.BigCrystallineIntrinsicGenerators.presheaf p k B σ a j).obj (op ((ι).obj Q)))
    (hz : (IntrinsicGenerators.BigCrystallineIntrinsicGenerators.generator p k B σ a j).app (op ((ι).obj Q)) z =
      (IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sourceSections p k B σ a j x).app (op ((ι).obj Q)) (1 : R)) :
    representative p k B σ a j x Q = z :=
  (ConcreteCategory.bijective_of_isIso
    ((IntrinsicGenerators.BigCrystallineIntrinsicGenerators.generator p k B σ a j).app (op ((ι).obj Q)))).injective
      ((generator_representative p k B σ a j x Q).trans hz.symm)

theorem coordinates (j : ℕ) (x : A₀ ⟶ (K).X j) (Q : Site.Object p k X) :
    (CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a j).hom.app (op Q)
      ((IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.targetSections p k B σ a j
        (IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.transport p k B σ a j x)).app (op Q) (1 : R)) =
    (IntrinsicGeneratorCoordinates.BigCrystallineIntrinsicGeneratorCoordinates.rawMap p k B σ a j).app (op Q)
      (representative p k B σ a j x Q) := by
  let s := IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sourceSections p k B σ a j x
  let c := ((IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom.f j).hom.app (op Q)
  let t := (CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a j).hom.app (op Q)
  let z := representative p k B σ a j x Q
  have hs := congrArg (fun s => s.app (op Q) (1 : R))
    (IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates.sections p k B σ a j x)
  have hz := IntrinsicGenerators.BigCrystallineIntrinsicGenerators.generator_representative p k B σ a j Q
    (s.app (op ((ι).obj Q)) (1 : R))
  have hg := congrArg (fun f => f.app (op Q) z)
    (IntrinsicGeneratorCoordinates.BigCrystallineIntrinsicGeneratorCoordinates.generator p k B σ a j)
  exact (congrArg (fun y => t y) hs).trans
    ((congrArg (fun y => t (c y)) hz.symm).trans hg)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGeneratorSections.BigCrystallineIntrinsicGeneratorSections
