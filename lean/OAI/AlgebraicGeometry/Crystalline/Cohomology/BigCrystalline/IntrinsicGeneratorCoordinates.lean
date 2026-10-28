import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationMap

/-! # Intrinsic Generator Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGeneratorCoordinates.BigCrystallineIntrinsicGeneratorCoordinates

noncomputable section

/-! # The original native comparison on actual big frame generators -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (B := W)
  (J := I) (δ := γ) (f := bX)
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := I) (δ := γ) (base := bX) a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k

theorem native_generator (n : ℕ) :
    toSheafify T ((L).X n ⋙ E) ≫ (CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a n).hom =
      𝟙 ((L).X n ⋙ E) :=
  (isoSheafify T (CoefficientSheaf.CrystallineCoefficientSheaf.isSheaf p k X ((L).X n)
    (CrystallineFrame.FormsSheaf.CrystallineFrameFormsSheaf.term_isSheaf p k B σ a n))).hom_inv_id

def rawMap (n : ℕ) : (ι).op ⋙ ((K).X n ⋙ E) ⟶ (L).X n ⋙ E :=
  whiskerRight ((IntrinsicResolution.BigCrystallineIntrinsicResolution.iso p k B σ a).hom.f n) E

theorem generator (n : ℕ) :
    whiskerLeft (ι).op (toSheafify U ((K).X n ⋙ E)) ≫
      (((IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom.f n).hom ≫
        (CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a n).hom) =
      rawMap p k B σ a n := by
  let η := whiskerLeft (ι).op (toSheafify U ((K).X n ⋙ E))
  let c := ((IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom.f n).hom
  let s := (CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a n).hom
  let f := rawMap p k B σ a n
  have hc : η ≫ c = f ≫ toSheafify T ((L).X n ⋙ E) :=
    SheafificationMap.SheafificationMapGenerators.generator T U ι ((K).X n ⋙ E) ((L).X n ⋙ E) f
  exact (Category.assoc η c s).symm.trans
    ((congrArg (fun t => t ≫ s) hc).trans
      ((Category.assoc f (toSheafify T ((L).X n ⋙ E)) s).trans
        ((congrArg (fun t => f ≫ t) (native_generator p k B σ a n)).trans (Category.comp_id f))))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGeneratorCoordinates.BigCrystallineIntrinsicGeneratorCoordinates
