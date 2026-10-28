import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Symbols
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialSymbol

/-! # Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Evaluation.WittPolynomialEvaluation

noncomputable section

/-! # Every finite ordinary form evaluates by the original frame algebra map -/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B P r hr hb
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B P r hr hb
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B P r hr hb
local notation "qA" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficientAlgHom p k B P r hr hb

def levelMap (m n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form W P n →ₗ[W]
    PD.PDDeRham.Form p k B Tower n m :=
  ((PD.DeRham.PDDeRham.relations W (T m).ring (RingHom.ker (T m).reduction)
    (T m).dividedPowers n).mkQ.restrictScalars W).comp
    (DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (qA m)) n)

omit [PerfectRing k p] [Fintype σ] [LinearOrder σ] in
theorem levelMap_symbol (m n : ℕ) (a : P) (v : Fin n → P) :
    levelMap p k σ m n (DeRhamPresentationTo.DeRhamPresentation.symbol W P a v) =
      PD.DeRham.PDDeRham.symbol W (T m).ring (RingHom.ker (T m).reduction) (T m).dividedPowers
        (q m a) (q m ∘ v) := by
  change (PD.DeRham.PDDeRham.relations W (T m).ring (RingHom.ker (T m).reduction) (T m).dividedPowers n).mkQ
    (DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (qA m)) n (DeRhamPresentationTo.DeRhamPresentation.symbol W P a v)) = _
  rw [DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  rfl

theorem eval_of (m n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form W P n) :
    PD.PDDeRham.eval p k B Tower n m
      ((PolynomialComplex.WittPolynomialComplex.complexIso p k σ).hom.f n (AdicCompletion.of I _ ω)) =
        levelMap p k σ m n ω := by
  let f : DeRhamPresentationTo.DeRhamPresentation.Form W P n →ₗ[W] PD.PDDeRham.Form p k B Tower n m :=
    (PD.PDDeRham.eval p k B Tower n m).comp
      (((PolynomialComplex.WittPolynomialComplex.complexIso p k σ).hom.f n).hom.comp
        (AdicCompletion.of I (DeRhamPresentationTo.DeRhamPresentation.Form W P n)))
  have h : f = levelMap p k σ m n := OrdinaryPolynomialSymbol.OrdinaryPolynomialSymbolExt.linearMap_ext W σ n f
    (levelMap p k σ m n) (fun a v =>
      (Symbols.WittPolynomialSymbols.eval_of_symbol p k σ n m a v).trans
        (levelMap_symbol p k σ m n a (MvPolynomial.X ∘ v)).symm)
  exact DFunLike.congr_fun h ω

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Evaluation.WittPolynomialEvaluation
