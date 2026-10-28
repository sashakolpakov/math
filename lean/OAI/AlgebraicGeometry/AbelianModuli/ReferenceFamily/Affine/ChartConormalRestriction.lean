import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalPrecomposition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleHomDerivation

/-! # Chart Conormal Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalRestriction

noncomputable section

/-! The constructed affine conormal coordinates commute with the
actual etale extension of derivations along an affine restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (B D : Type) [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] (q : B →ₐ[k] D) (hq : q.toRingHom.Etale)
    (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom]
    (iB : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) (iD : EtaleSplittingAt.EtaleSplitting.affineOver k D ⟶ A)
    [IsOpenImmersion iB.left] [IsOpenImmersion iD.left]

theorem affineChartCoefficientConormalEquiv_restriction
    (hi : AlgebraAutomorphismNaturality.affineOverAlgHom k B D q ≫ iB = iD) (d : Derivation k B B)
    (z : Constructed.IdentityConormal.constructedIdentityConormal k A) :
    ChartCoefficientConormal.affineChartCoefficientConormalEquiv k D D A iD (EtaleHomDerivation.etaleAlgHomDerivationLinear q hq d) z =
      q (ChartCoefficientConormal.affineChartCoefficientConormalEquiv k B B A iB d z) := by
  let : Algebra B D := q.toRingHom.toAlgebra
  let : IsScalarTower k B D := IsScalarTower.of_algebraMap_eq (fun c => (q.commutes c).symm)
  let q₀ : B →ₐ[B] D := Algebra.ofId B D
  have hp : Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D D (EtaleHomDerivation.etaleAlgHomDerivationLinear q hq d) =
      Dual.CoefficientLiftNaturality.coefficientDerivationMap k B B D q₀ d := by
    apply Derivation.ext
    intro b
    exact EtaleHomDerivation.etaleAlgHomDerivationLinear_map q hq d b
  have hi' : AlgebraAutomorphismNaturality.affineOverAlgHom k B D (IsScalarTower.toAlgHom k B D) ≫ iB = iD := hi
  have hc := ChartConormalPrecomposition.affineChartCoefficientConormalEquiv_precomposition k B D D A iB iD hi'
    (EtaleHomDerivation.etaleAlgHomDerivationLinear q hq d)
  rw [hp] at hc
  exact (congrArg (fun f => f z) hc).symm.trans
    (ChartConormalNaturality.affineChartCoefficientConormalEquiv_natural k B B D q₀ A iB d z)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalRestriction
