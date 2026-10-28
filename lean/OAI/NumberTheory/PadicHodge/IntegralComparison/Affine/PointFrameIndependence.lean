import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointParameterIndependence
import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialConormalBasis
import Mathlib.RingTheory.Etale.Basic

/-! # Point Frame Independence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointFrameIndependence

noncomputable section

/-! The original affine point coefficient is independent of a full
regular equation tuple when each tuple uses its own differential frame.
The matching conormal bases and zero-dimensional quotient basis are derived. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) (K : ChainComplex Y.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent]
  (M : Y.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (I : Ideal Γ(Y, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ I))
  [∀ q, ((LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  {k : Type u} [CommRing k] [Algebra k Γ(Y, U)]
  [Algebra.Smooth k Γ(Y, U)] (eI : (Γ(Y, U) ⧸ I) ≃ₐ[k] k)
  {n : ℕ} (s : Fin n → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (b : Module.Basis (Fin n) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hb : (b : Fin n → Ω[Γ(Y, U)⁄k]) = fun i => KaehlerDifferential.D k Γ(Y, U) (s i))
  (t : Fin n → Γ(Y, U))
  (ht : Koszul.OrientedTopCohomology.ideal Γ(Y, U) t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn t))
  (bt : Module.Basis (Fin n) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hbt : (bt : Fin n → Ω[Γ(Y, U)⁄k]) = fun i => KaehlerDifferential.D k Γ(Y, U) (t i))
  (e : (AffineOpen.InternalHom.sections U hU).obj N ≃ₗ[Γ(Y, U)] ⋀[Γ(Y, U)]^n Ω[Γ(Y, U)⁄k])

include eI hb hbt in
theorem independent :
    (OrientedPurity.iso U hU N K M ε I eM s hs hreg
      (ParameterLineAdjunction.frame (c := n) (g := 0) b ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom =
    (OrientedPurity.iso U hU N K M ε I eM t ht htreg
      (ParameterLineAdjunction.frame (c := n) (g := 0) bt ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom := by
  let : Algebra.Smooth k (Γ(Y, U) ⧸ I) := Algebra.Smooth.of_equiv eI.symm
  let : Algebra.FormallyEtale k (Γ(Y, U) ⧸ I) := Algebra.FormallyEtale.of_equiv eI.symm
  exact PointParameterIndependence.independent U hU N K M ε I eM
    s hs hreg (DifferentialConormalBasis.basis I s hs b hb)
    (DifferentialConormalBasis.basis_apply I s hs b hb)
    (Module.Basis.empty Ω[Γ(Y, U) ⧸ I⁄k]) b hb e
    t ht htreg (DifferentialConormalBasis.basis I t ht bt hbt)
    (DifferentialConormalBasis.basis_apply I t ht bt hbt) bt hbt

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointFrameIndependence
