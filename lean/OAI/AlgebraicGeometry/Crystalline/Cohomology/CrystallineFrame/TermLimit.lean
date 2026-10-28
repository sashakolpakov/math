import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FunctionLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FiniteSplitting
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ConeSections

/-! # Term Limit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TermLimit.CrystallineFrameTermLimit

noncomputable section

/-!
# Every native frame term has completed tensor sections

Finite free tensoring preserves the proved frame-function limit. Its
universal property identifies actual native presheaf sections, in each
degree, with tensor forms of the original completed PD envelope.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff) [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "Native" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "Completed" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower

local instance indexFintype (n : ℕ) : Fintype (Set.powersetCard σ n) := Fintype.ofFinite _

def termIso (n : ℕ) : F ⋙ Finite.TensorSheaf.FiniteTensorSheaf.tensor W (⋀[W]^n (σ →₀ W)) ≅ (K).X n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

def cone (n : ℕ) : Cone ((K).X n) :=
  (Cone.postcompose (termIso p k B σ r n).hom).obj
    ((Finite.TensorSheaf.FiniteTensorSheaf.tensor W (⋀[W]^n (σ →₀ W))).mapCone
      (FunctionLimit.CrystallineFrameFunctionLimit.completedCone p k B σ r hr hbase))

def isLimit (n : ℕ) : IsLimit (cone p k B σ r hr hbase n) := by
  let : PreservesLimitsOfSize.{u, u + 1} (Finite.TensorSheaf.FiniteTensorSheaf.tensor W (⋀[W]^n (σ →₀ W))) :=
    Finite.TensorSheaf.FiniteTensorSheaf.tensor_preservesLimits W (Set.powersetCard σ n) (⋀[W]^n (σ →₀ W))
      (FiniteSplitting.CrystallineFrameFiniteSplitting.basis p k σ n)
  exact (IsLimit.postcomposeHomEquiv (termIso p k B σ r n) _).symm
    (isLimitOfPreserves (Finite.TensorSheaf.FiniteTensorSheaf.tensor W (⋀[W]^n (σ →₀ W)))
      (FunctionLimit.CrystallineFrameFunctionLimit.completedConeIsLimit p k B σ r hr hbase))

def sectionsEquiv (n : ℕ) :
    ((Functor.const Nativeᵒᵖ).obj (ModuleCat.of W W) ⟶ (K).X n) ≃ₗ[W]
      Koszul.Tensor.KoszulTensor.Term W σ Completed n :=
  Module.ConeSections.ModuleConeSections.sectionsEquiv W (cone p k B σ r hr hbase n) (isLimit p k B σ r hr hbase n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TermLimit.CrystallineFrameTermLimit
