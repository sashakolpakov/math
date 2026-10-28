import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.BaseIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedSource
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Reduced Base Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseIso.IntrinsicPadicGeometricReducedBaseIso

noncomputable section

/-! Geometric pullback preserves the original Witt-to-p-adic
coordinate identification after every prime-power coefficient quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X Y : Over (Spec (CommRingCat.of ℤ_[p]))} (u : X ⟶ Y) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "IW" => (Ideal.span {(p : WittVector p (ZMod p))}) ^ (n + 1)
local notation "IZ" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)
local notation "S" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))

def targetMap : T ⋙ IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.target p Y n ⟶
    S ⋙ IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.target p X n :=
  Functor.whiskerRight (Affine.PairSectionAlgebraPullback.AffinePairSectionAlgebraPullback.transformation ℤ_[p] u)
    (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p] ⋙
      (IntegralComparison.Module.IdealQuotient.functor ℤ_[p] IZ).mapHomologicalComplex (.up ℕ) ⋙
        (G).mapHomologicalComplex (.up ℕ))

theorem component (U : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    (ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n).app U ≫
      (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n).hom.app ((S).obj U) =
    (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p Y n).hom.app ((T).obj U) ≫ (targetMap p u n).app U := by
  let Q := (IntegralComparison.Module.IdealQuotient.functor W IW).mapHomologicalComplex (.up ℕ)
  let a := (BaseIso.IntrinsicPadicGeometricBaseIso.wittMap p u).app U
  let b := (IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app ((S).obj U)
  let c := (IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p Y).hom.app ((T).obj U)
  let d := (BaseIso.IntrinsicPadicGeometricBaseIso.padicMap p u).app U
  have h₁ : Q.map a ≫ Q.map b = Q.map c ≫ Q.map d :=
    (Q.map_comp a b).symm.trans
      ((congrArg Q.map (BaseIso.IntrinsicPadicGeometricBaseIso.component p u U)).trans (Q.map_comp c d))
  let z := (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p]).map
    ((Affine.PairSectionAlgebraPullback.AffinePairSectionAlgebraPullback.transformation ℤ_[p] u).app U)
  have h₂ := ((NatIso.mapHomologicalComplex (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.coefficientIso p n) (.up ℕ)).hom).naturality z
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

theorem naturality : ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n ≫
    Functor.whiskerLeft S (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n).hom =
      Functor.whiskerLeft T (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p Y n).hom ≫ targetMap p u n := by
  apply NatTrans.ext
  funext U
  exact component p u n U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseIso.IntrinsicPadicGeometricReducedBaseIso
