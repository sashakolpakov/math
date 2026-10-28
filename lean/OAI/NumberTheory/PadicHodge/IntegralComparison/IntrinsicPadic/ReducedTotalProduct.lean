import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso

/-! # Reduced Total Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedTotalProduct.Intrinsic

noncomputable section

/-! The actual finite ordinary-quotient-to-PD comparison preserves
products on Čech cohomology and is a quasi-isomorphism on the original
integral coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "Ip" => (Ideal.span {(p : W)}) ^ (n+1)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex W Ip A
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DiagramProduct.complex w H
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing W Ip A
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DiagramProduct.pairing w H
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def map := Cech.ComplexDiagramNaturality.Coordinates.complexMap a

omit [IsProper X.hom] [X.left.IsSeparated] in
theorem map_pairing (i j : ℕ) (V : X.left.affineOpensᵒᵖ)
    (x : ((P).X i).obj V) (y : ((P).X j).obj V) :
    ((Intrinsic.map p X Y f hp n).f (i+j)).app V (μ i j V x y) =
      ν i j V (((Intrinsic.map p X Y f hp n).f i).app V x)
        (((Intrinsic.map p X Y f hp n).f j).app V y) :=
  ReducedProduct.Intrinsic.map_pairing p X Y f hp n i j V x y

abbrev totalMap := Presheaf.CechProductNaturality.totalMap N (Intrinsic.map p X Y f hp n)

abbrev cohomologyMap_cup := Presheaf.CohomologyProduct.Cech.totalMap_cohomologyCup N P μ
  (OrdinaryQuotientDiagramProduct.Ordinary.natural W Ip A)
  (OrdinaryQuotientDiagramProduct.Ordinary.differential W Ip A) Q ν
  (Frame.DiagramProduct.natural w H) (Frame.DiagramProduct.differential w H)
  (Intrinsic.map p X Y f hp n) (map_pairing p X Y f hp n)

theorem quasiIso : QuasiIso (totalMap p X Y f hp n) := by
  apply AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.quasiIso W N (Intrinsic.map p X Y f hp n)
  intro j b
  let V : X.left.affineOpens := ∏ᶜ (U ∘ b)
  let : IsIso ((a).app (op V)) := GeometricComparison.IntrinsicPadic.ReducedDeRhamIso.IntrinsicPadicReducedDeRhamIso.pd_component_isIso
    p X Y f hp n V (b 0) (leOfHom (Pi.π (U ∘ b) 0))
  change QuasiIso ((a).app (op V))
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedTotalProduct.Intrinsic
