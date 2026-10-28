import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicExtComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.GlobalAcyclic

/-! # Frame Global Acyclic -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic

noncomputable section

/-! # Acyclicity of the original big crystalline polynomial frame terms -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] (a : σ → B)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.restriction p k B
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a

def termIso (j : ℕ) : (F).obj ((K).X j) ≅ (L).X j :=
  (HomologicalComplex.eval _ (.up ℕ) j).mapIso (IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a)

def termEquiv (j n : ℕ) : Ext.{u + 2} A ((K).X j) n ≃ₗ[R]
    Ext.{u + 2} (Site.coefficientSheaf p k X) ((L).X j) n :=
  (IntrinsicExtComparison.BigCrystallineIntrinsicExtComparison.equivalence p k B ((K).X j) n).trans
    (NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius.extIsoCongr R (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.constantIso p k B)
      (termIso p k B σ a j) n)

variable (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

include hr hbase in
theorem term (j n : ℕ) (α : Ext.{u + 2} A
    ((FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX (fun i => r (MvPolynomial.X i))).X j) (n + 1)) :
    α = 0 := by
  apply (termEquiv p k B σ (fun i => r (MvPolynomial.X i)) j (n + 1)).injective
  rw [map_zero]
  exact CrystallineFrame.GlobalAcyclic.CrystallineFrameGlobalAcyclic.term p k B σ r hr hbase j n _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic
