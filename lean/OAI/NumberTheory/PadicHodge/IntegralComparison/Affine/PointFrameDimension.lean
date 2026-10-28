import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointFrameIndependence

/-! # Point Frame Dimension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointFrameDimension

noncomputable section

/-! Parameter independence with the geometric ambient dimension kept
separate from the length of the full regular equation tuple. -/
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
  {r d : ℕ} (h : r = d)
  (s : Fin r → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (b : Module.Basis (Fin d) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hb : (fun i : Fin r => b (Fin.cast h i)) = fun i => KaehlerDifferential.D k Γ(Y, U) (s i))
  (t : Fin r → Γ(Y, U))
  (ht : Koszul.OrientedTopCohomology.ideal Γ(Y, U) t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn t))
  (bt : Module.Basis (Fin d) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hbt : (fun i : Fin r => bt (Fin.cast h i)) = fun i => KaehlerDifferential.D k Γ(Y, U) (t i))
  (e : (AffineOpen.InternalHom.sections U hU).obj N ≃ₗ[Γ(Y, U)] ⋀[Γ(Y, U)]^d Ω[Γ(Y, U)⁄k])

include eI h hb hbt in
theorem independent :
    (OrientedPurity.iso U hU N K M ε I eM s hs hreg
      (ParameterLineAdjunction.frame (c := d) (g := 0) b ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom =
    (OrientedPurity.iso U hU N K M ε I eM t ht htreg
      (ParameterLineAdjunction.frame (c := d) (g := 0) bt ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom := by
  subst d
  exact PointFrameIndependence.independent U hU N K M ε I eM eI
    s hs hreg b hb t ht htreg bt hbt e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointFrameDimension
