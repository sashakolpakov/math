import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.CoefficientDetection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.CoefficientCharacters
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ConormalOperations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalNaturality

/-! # Coefficient Conormal Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CoefficientConormalLinearity

noncomputable section

/-! The constructed affine-chart conormal comparison is linear over
every reduced finite-type complex coefficient algebra. Actual complex
characters detect the identities, and all pointwise comparisons are
the already proved native tangent maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [GrpObj X]
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ X) [IsOpenImmersion i.left]
    (C : Type) [CommRing C] [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C]
    [Algebra.FiniteType ℂ C] [IsReduced C]

local notation "F" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B C X i

theorem regularCoefficientConormal_add (d e : Derivation ℂ B C) : F (d + e) = F d + F e := by
  apply LinearMap.ext
  intro z
  apply Complex.CoefficientDetection.complexCoefficientCharacters_ext C
  intro q
  let := Complex.CoefficientCharacters.ComplexCoefficientCharacter.algebra B C q
  let := Complex.CoefficientCharacters.ComplexCoefficientCharacter.scalarTower B C q
  let q₀ := Complex.CoefficientCharacters.ComplexCoefficientCharacter.map B C q
  let R := Dual.CoefficientLiftNaturality.coefficientDerivationMap ℂ B C ℂ q₀
  have hn (d : Derivation ℂ B C) : q (F d z) = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (R d) z :=
    (Affine.ChartConormalNaturality.affineChartCoefficientConormalEquiv_natural ℂ B C ℂ q₀ X i d z).symm
  calc
    q (F (d + e) z) = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (R (d + e)) z := hn (d + e)
    _ = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (R d + R e) z :=
      congrArg (fun a => Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i a z) (R.map_add d e)
    _ = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (R d) z + Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (R e) z :=
      congrArg (fun f => f z) (Complex.ConormalOperations.complexConormal_add X B i (R d) (R e))
    _ = q (F d z) + q (F e z) := congrArg₂ (· + ·) (hn d).symm (hn e).symm
    _ = q ((F d + F e) z) := (q.map_add _ _).symm

theorem regularCoefficientConormal_smul (c : C) (d : Derivation ℂ B C) : F (c • d) = c • F d := by
  apply LinearMap.ext
  intro z
  apply Complex.CoefficientDetection.complexCoefficientCharacters_ext C
  intro q
  let := Complex.CoefficientCharacters.ComplexCoefficientCharacter.algebra B C q
  let := Complex.CoefficientCharacters.ComplexCoefficientCharacter.scalarTower B C q
  let q₀ := Complex.CoefficientCharacters.ComplexCoefficientCharacter.map B C q
  let R := Dual.CoefficientLiftNaturality.coefficientDerivationMap ℂ B C ℂ q₀
  have hn (d : Derivation ℂ B C) : q (F d z) = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (R d) z :=
    (Affine.ChartConormalNaturality.affineChartCoefficientConormalEquiv_natural ℂ B C ℂ q₀ X i d z).symm
  have hR : R (c • d) = q c • R d := CoefficientDerivationMapSemilinear.coefficientDerivationMap_smul ℂ B C ℂ q₀ c d
  calc
    q (F (c • d) z) = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (R (c • d)) z := hn (c • d)
    _ = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (q c • R d) z :=
      congrArg (fun a => Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i a z) hR
    _ = q c • Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (R d) z :=
      congrArg (fun f => f z) (Complex.ConormalOperations.complexConormal_smul X B i (q c) (R d))
    _ = q c • q (F d z) := congrArg (fun a => q c • a) (hn d).symm
    _ = q ((c • F d) z) := (q.map_mul _ _).symm

def regularCoefficientConormalLinearEquiv : Derivation ℂ B C ≃ₗ[C] (Constructed.IdentityConormal.constructedIdentityConormal ℂ X →ₗ[ℂ] C) where
  toEquiv := F
  map_add' := regularCoefficientConormal_add X B i C
  map_smul' := regularCoefficientConormal_smul X B i C

theorem regularCoefficientConormalLinearEquiv_apply (d : Derivation ℂ B C) :
    regularCoefficientConormalLinearEquiv X B i C d = F d := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CoefficientConormalLinearity
