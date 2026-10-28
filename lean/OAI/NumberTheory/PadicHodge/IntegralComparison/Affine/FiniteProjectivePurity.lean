import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.Purity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalExactness

/-! # Finite Projective Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FiniteProjectivePurity

noncomputable section

/-! Native affine internal-Hom purity for finite projective coefficients
over the actual quotient coordinate algebra. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (K : ChainComplex X.Modules ℕ)
  [∀ i, (K.X i).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ i, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  (Q : Type u) [CommRing Q] [Algebra Γ(X, U) Q]
  (C : Type u) [AddCommGroup C] [Module Q C] [Module Γ(X, U) C]
  [IsScalarTower Γ(X, U) Q C] [Module.Finite Q C] [Module.Projective Q C]
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) C)
  (rs : List Γ(X, U)) (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) rs)
  (eQ : IntegralComparison.ProjectiveResolution.DualPurity.quotient Γ(X, U) rs ≅ ModuleCat.of Γ(X, U) Q)
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

def resolution : ProjectiveResolution (ModuleCat.of Γ(X, U) C) :=
  IntegralComparison.ProjectiveResolution.Transport.alongIso
    (AffineOpen.Resolution.ofAugmentation U hU M K ε) eM

include ε hreg eQ eN eM in
theorem linear_exactAt (n : ℕ) (hn : n ≠ rs.length) :
    ((((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op)).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (HomologicalComplex.homologyMapIso
    (LinearResolutionPurity.sectionComplexIso U hU N K) n).isZero_iff.mpr
  let P0 := IntegralComparison.ProjectiveResolution.DualPurity.koszul Γ(X, U) rs hreg
  let P := IntegralComparison.ProjectiveResolution.Transport.alongIso P0 eQ
  let PM := resolution U hU K M ε C eM
  have h0 := LinearHomDualPurity.exactAt Γ(X, U) rs hreg P0
    ((AffineOpen.InternalHom.sections U hU).obj N) eN n hn
  have h := ProjectiveCoefficient.Purity.exactAt Γ(X, U) Q
    ((AffineOpen.InternalHom.sections U hU).obj N) n P C PM h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h

include ε hreg eQ eN eM in
theorem exactAt (n : ℕ) (hn : n ≠ rs.length) :
    (LocalExactness.sectionComplex
      (LinearResolutionPurity.internalComplex N K) U).ExactAt n := by
  let J := (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op)
  have h : J.ExactAt n := linear_exactAt U hU N K M ε Q C eM rs hreg eQ eN n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  let G := forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat
  exact ((J.sc n).mapHomologyIso G).isZero_iff.mpr (G.map_isZero h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FiniteProjectivePurity
