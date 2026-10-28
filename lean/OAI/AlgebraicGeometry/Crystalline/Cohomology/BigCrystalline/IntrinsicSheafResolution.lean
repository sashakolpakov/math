import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport

/-! # Intrinsic Sheaf Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution

noncomputable section

/-! # The original big and native frame sheaf resolutions are isomorphic -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.restriction p k B
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := I) (δ := γ) (base := bX) a

def iso : ((F).mapHomologicalComplex (.up ℕ)).obj
    (FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a) ≅
      CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a :=
  (Functor.mapHomologicalComplexCompIso (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.comparisonIso p k B) (.up ℕ)).app K ≪≫
    ((S).mapHomologicalComplex (.up ℕ)).mapIso (IntrinsicResolution.BigCrystallineIntrinsicResolution.iso p k B σ a)

theorem component (n : ℕ) : (iso p k B σ a).hom.f n =
    (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.comparisonIso p k B).hom.app ((K).X n) ≫
      (S).map ((IntrinsicResolution.BigCrystallineIntrinsicResolution.iso p k B σ a).hom.f n) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution
