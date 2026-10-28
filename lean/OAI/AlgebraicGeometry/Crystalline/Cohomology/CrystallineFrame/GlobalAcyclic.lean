import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.ExtVanishing
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FiniteSplitting
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.SplitExtVanishing

/-! # Global Acyclic -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.GlobalAcyclic.CrystallineFrameGlobalAcyclic

noncomputable section

/-!
# Global acyclicity of every actual finite frame-resolution term

Framed global vanishing and the exact frame adjunction give positive Ext
vanishing for native frame functions. The natural finite coefficient
splitting of each exterior degree gives the same vanishing for every
term of the original sheaf resolution.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X

include hr hbase in
theorem functions (n : ℕ)
    (α : Abelian.Ext (Site.coefficientSheaf p k X) ((S).obj F) (n + 1)) : α = 0 :=
  Finite.SplitExtVanishing.FiniteSplitExtVanishing.of_targetIso
    (FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction.structureSheafIso p k B σ a) (n + 1)
    (FramedPolynomial.ExtVanishing.FramedPolynomialExtVanishing.nativeFrame p k B σ r hr hbase n) α

variable [Fintype σ]

include hr hbase in
theorem term (j n : ℕ)
    (α : Abelian.Ext (Site.coefficientSheaf p k X)
      ((SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X j) (n + 1)) : α = 0 := by
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Fintype (Set.powersetCard σ j) := Fintype.ofFinite _
  exact Finite.SplitExtVanishing.FiniteSplitExtVanishing.of_splitting (fun _ : Set.powersetCard σ j => (S).obj F)
    (FiniteSplitting.CrystallineFrameFiniteSplitting.sheafProjection p k B σ a j)
    (FiniteSplitting.CrystallineFrameFiniteSplitting.sheafInclusion p k B σ a j)
    (FiniteSplitting.CrystallineFrameFiniteSplitting.sheaf_sum_identity p k B σ a j)
    (n + 1) (fun _ => functions p k B σ r hr hbase n) α

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.GlobalAcyclic.CrystallineFrameGlobalAcyclic
