import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ParameterAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AdjunctionIndependence

/-! # Point Parameter Independence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointParameterIndependence

noncomputable section

/-! At a section, the coefficient in the matching top differential
frame is independent of its regular parameters. Both coefficients are
coordinates of the same intrinsic degree-zero adjunction class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Module
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

private theorem zero_symbol (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (a : A) (v : Fin 0 → A) :
    exteriorPower.zeroEquiv A Ω[A⁄k]
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior k A 0
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k A a v)) = a := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol]
  change exteriorPower.zeroEquiv A Ω[A⁄k]
    (a • exteriorPower.ιMulti A 0 (fun i => KaehlerDifferential.D k A (v i))) = a
  rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]

private theorem ambient_eq {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (I : Ideal A) {c : ℕ} (b bt : Basis (Fin c) A Ω[A⁄k])
    (N : ModuleCat.{u} A) (e : N ≃ₗ[A] ⋀[A]^c Ω[A⁄k]) :
    ParameterLineAdjunction.ambient (c := c) (g := 0) I b N e =
      ParameterLineAdjunction.ambient (c := c) (g := 0) I bt N e :=
  congrArg (fun z => (e.baseChange A (A ⧸ I) N _).trans z)
    (TopExteriorBaseChange.independent_basis (A ⧸ I) b bt)

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) (K : ChainComplex Y.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent]
  (M : Y.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (I : Ideal Γ(Y, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ I))
  [∀ q, ((LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(Y, U) Γ(Y, U))
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (bI : Basis (Fin c) (Γ(Y, U) ⧸ I) I.Cotangent)
  (hI : ∀ i, bI i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(Y, U) I s hs i))
  {k : Type u} [CommRing k] [Algebra k Γ(Y, U)]
  [Algebra.Smooth k Γ(Y, U)] [Algebra.Smooth k (Γ(Y, U) ⧸ I)]
  (bQ : Basis (Fin 0) (Γ(Y, U) ⧸ I) Ω[Γ(Y, U) ⧸ I⁄k])
  (b : Basis (Fin c) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hb : (b : Fin c → Ω[Γ(Y, U)⁄k]) = fun i => KaehlerDifferential.D k Γ(Y, U) (s i))
  (e : (AffineOpen.InternalHom.sections U hU).obj N ≃ₗ[Γ(Y, U)] ⋀[Γ(Y, U)]^c Ω[Γ(Y, U)⁄k])

include hI hb in
theorem coefficient (x : (ModuleExactSections.sections U).obj
    ((LinearResolutionPurity.internalComplex N K).homology c)) :
    exteriorPower.zeroEquiv (Γ(Y, U) ⧸ I) Ω[Γ(Y, U) ⧸ I⁄k]
      ((DualizingAdjunction.iso U hU N K M ε I eM eN s hs hreg bI bQ
        (ParameterLineAdjunction.ambient (c := c) (g := 0) I b ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom x) =
    (OrientedPurity.iso U hU N K M ε I eM s hs hreg
      (ParameterLineAdjunction.frame (c := c) (g := 0) b ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom x := by
  have hb' : (b : Fin (c + 0) → Ω[Γ(Y, U)⁄k]) =
      Fin.append (fun i => KaehlerDifferential.D k Γ(Y, U) (s i))
        (fun i : Fin 0 => KaehlerDifferential.D k Γ(Y, U) (Fin.elim0 i)) := by
    rw [hb]
    funext i
    simpa only [Fin.castAdd_zero, Fin.cast_eq_self] using
      (Fin.append_left (fun j => KaehlerDifferential.D k Γ(Y, U) (s j))
        (fun j : Fin 0 => KaehlerDifferential.D k Γ(Y, U) (Fin.elim0 j)) i).symm
  have h := ParameterAdjunction.symbol U hU N K M ε I eM eN s hs hreg bI hI
    bQ (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) b hb' e x
  exact (congrArg (exteriorPower.zeroEquiv (Γ(Y, U) ⧸ I) Ω[Γ(Y, U) ⧸ I⁄k]) h).trans
    (zero_symbol k (Γ(Y, U) ⧸ I) _ _)

variable (t : Fin c → Γ(Y, U))
  (ht : Koszul.OrientedTopCohomology.ideal Γ(Y, U) t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn t))
  (btI : Basis (Fin c) (Γ(Y, U) ⧸ I) I.Cotangent)
  (htI : ∀ i, btI i = I.toCotangent (ConormalKoszulPurity.conormalVectors Γ(Y, U) I t ht i))
  (bt : Basis (Fin c) Γ(Y, U) Ω[Γ(Y, U)⁄k])
  (hbt : (bt : Fin c → Ω[Γ(Y, U)⁄k]) = fun i => KaehlerDifferential.D k Γ(Y, U) (t i))

attribute [local irreducible] OrientedPurity.iso DualizingAdjunction.iso
  ParameterLineAdjunction.frame ParameterLineAdjunction.ambient

include hI hb htI hbt bQ in
theorem independent :
    (OrientedPurity.iso U hU N K M ε I eM s hs hreg
      (ParameterLineAdjunction.frame (c := c) (g := 0) b ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom =
    (OrientedPurity.iso U hU N K M ε I eM t ht htreg
      (ParameterLineAdjunction.frame (c := c) (g := 0) bt ((AffineOpen.InternalHom.sections U hU).obj N) e)).hom := by
  let eN := ParameterLineAdjunction.frame (c := c) (g := 0) b ((AffineOpen.InternalHom.sections U hU).obj N) e
  have hi := AdjunctionIndependence.independent U hU N K M ε I eM eN eN
    s hs hreg bI hI t ht htreg btI htI bQ bQ
    (ParameterLineAdjunction.ambient (c := c) (g := 0) I b ((AffineOpen.InternalHom.sections U hU).obj N) e)
    (ParameterLineAdjunction.ambient (c := c) (g := 0) I bt ((AffineOpen.InternalHom.sections U hU).obj N) e)
    (ambient_eq I b bt ((AffineOpen.InternalHom.sections U hU).obj N) e)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (coefficient U hU N K M ε I eM eN s hs hreg bI hI bQ b hb e x).symm.trans
    ((congrArg (fun a => exteriorPower.zeroEquiv (Γ(Y, U) ⧸ I) Ω[Γ(Y, U) ⧸ I⁄k]
      (a.hom x)) hi).trans
        (coefficient U hU N K M ε I eM eN t ht htreg btI htI bQ bt hbt e x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.PointParameterIndependence
