import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameSource
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationMapZero

/-! # Frobenius Frame Truncation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameTruncation.IntrinsicPadicFrobeniusFrameTruncation

noncomputable section

/-! Actual native frame Frobenius kills the first Hodge truncation,
including after the original reduced-integral-to-frame comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

def source : CochainComplex (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp 0)

def map : source p X Y f hp ⟶ source p X Y f hp :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (FrobeniusFrameSource.IntrinsicPadicFrobeniusFrameSource.transformation p X Y f hp)

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem positive (n : ℕ) (hn : 0 < n) : (IntrinsicPadicFrobeniusFrameTruncation.map p X Y f hp).f n = 0 := by
  apply NatTrans.ext
  funext U
  exact FrobeniusFrameSource.IntrinsicPadicFrobeniusFrameSource.positive p X Y f hp U.unop n hn

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem truncation : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (source p X Y f hp) 1 ≫ IntrinsicPadicFrobeniusFrameTruncation.map p X Y f hp = 0 :=
  TruncationMapZero.HodgeTruncationMapZero.mapped (𝟭 (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R))
    (K := source p X Y f hp) (IntrinsicPadicFrobeniusFrameTruncation.map p X Y f hp) 1 (fun n hn => positive p X Y f hp n (by omega))

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem integral_source_zero : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X 0)) 1 ≫
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp 0) ≫
        IntrinsicPadicFrobeniusFrameTruncation.map p X Y f hp = 0 :=
  TruncationMapZero.HodgeTruncationMapZero.after_map (𝟭 (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R))
    (K := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X 0))
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp 0))
    (IntrinsicPadicFrobeniusFrameTruncation.map p X Y f hp) 1 (fun n hn => positive p X Y f hp n (by omega))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameTruncation.IntrinsicPadicFrobeniusFrameTruncation
