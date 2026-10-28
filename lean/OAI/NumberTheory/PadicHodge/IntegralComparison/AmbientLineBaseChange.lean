import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedResidueRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameBaseChange

/-! # Ambient Line Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AmbientLineBaseChange

noncomputable section

/-! A compatible line-to-top-form map commutes with ambient quotient
restriction. This tensor calculation is independent of sheaf choices. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham
open OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedResidueRestriction.Conormal

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (r : A) [IsLocalization.Away r B] (I : Ideal A) (J : Ideal B)
  (hJ : I.map (algebraMap A B) = J) (hIJ : I ≤ J.comap (algebraMap A B))
  (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) (f : M →ₛₗ[algebraMap A B] N) (n : ℕ)
  (eA : M ≃ₗ[A] ⋀[A]^n Ω[A⁄k]) (eB : N ≃ₗ[B] ⋀[B]^n Ω[B⁄k])
  (eI : (A ⧸ I) ⊗[A] M ≃ₗ[A ⧸ I] ⋀[A ⧸ I]^n ((A ⧸ I) ⊗[A] Ω[A⁄k]))
  (eJ : (B ⧸ J) ⊗[B] N ≃ₗ[B ⧸ J] ⋀[B ⧸ J]^n ((B ⧸ J) ⊗[B] Ω[B⁄k]))
  (heI : ∀ a m, eI (a ⊗ₜ[A] m) = GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap A (A ⧸ I) Ω[A⁄k] n (a ⊗ₜ[A] eA m))
  (heJ : ∀ b m, eJ (b ⊗ₜ[B] m) = GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap B (B ⧸ J) Ω[B⁄k] n (b ⊗ₜ[B] eB m))
  (hcomp : ∀ m, eB (f m) =
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (Exterior.KaehlerBaseChange.algebraHom (k := k) (A := A) (B := B)) n (eA m))

include heI heJ hcomp in
theorem restriction (x : (A ⧸ I) ⊗[A] M) :
    LocalizedResidueRestriction.Conormal.exteriorRestrictionOfEq r I J hJ n (eI x) =
      eJ (LineFrameBaseChange.lineMap A B (algebraMap A B) I J hIJ M N f x) := by
  subst J
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [LocalizedResidueRestriction.Conormal.exteriorRestrictionOfEq, TensorProduct.tmul_add, map_add] at hx hy ⊢
    rw [hx, hy]
  | tmul a m =>
    change LocalizedAmbientExteriorRestriction.ConormalResidue.exteriorMap r I n (1 ⊗ₜ[A ⧸ I] eI (a ⊗ₜ[A] m)) = _
    rw [heI, LineFrameBaseChange.lineMap_tmul, heJ, hcomp]
    exact LocalizedAmbientExteriorRestriction.ConormalResidue.exteriorMap_scalar_tmul r I n a (eA m)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AmbientLineBaseChange
