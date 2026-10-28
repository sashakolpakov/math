import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.IsogenyEtale
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedGeometricPointDetection
import Mathlib.GroupTheory.OrderOfElement

/-! # Kernel Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Multiplication by the specified finite-flat degree annihilates the actual polarization kernel over arbitrary bases. Geometric point annihilation is promoted to scheme equality through its unramified structure. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u

variable {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernelMultiplication_degree_eq_zero
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i) :
    p.kernelMultiplication ((∏ i, δ i) ^ 2) = toUnit p.kernelScheme ≫ p.kernelZeroSection := by
  have : FormallyUnramified p.kernelScheme.hom := hp.kernel_formallyUnramified hδ
  have : IsClosedImmersion p.kernelInclusion.left := p.kernelInclusion_closedImmersion
  have : Mono p.kernelInclusion := Over.mono_of_mono_left p.kernelInclusion
  apply UnramifiedGeometricPointDetection.unramified_overHom_eq_of_geometricFieldPoints
  intro K _ _ s
  let T : Over S := Over.mk (s ≫ p.kernelScheme.hom)
  let y : T ⟶ p.kernelScheme := Over.homMk s rfl
  let t : p.kernelAt T := p.kernelSchemePointsEquiv T y
  have hc : Nat.card (p.kernelAt T) = (∏ i, δ i) ^ 2 :=
    (Nat.card_congr (p.kernelGeometricPointsEquiv (s ≫ p.kernelScheme.hom))).symm.trans
      (hp.kernel_geometricBaseChange_points_card hδ K (s ≫ p.kernelScheme.hom))
  have ht : t ^ ((∏ i, δ i) ^ 2) = 1 := by
    rw [← hc]
    exact pow_card_eq_one'
  have hv : (y ≫ p.kernelInclusion) ^ ((∏ i, δ i) ^ 2) = 1 := congrArg Subtype.val ht
  have H : y ≫ p.kernelMultiplication ((∏ i, δ i) ^ 2) =
      y ≫ (toUnit p.kernelScheme ≫ p.kernelZeroSection) := by
    apply (cancel_mono p.kernelInclusion).mp
    calc
      _ = (y ≫ p.kernelInclusion) ^ ((∏ i, δ i) ^ 2) := by
        rw [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelMultiplication_inclusion, MonObj.comp_pow]
      _ = 1 := hv
      _ = _ := by simp only [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelZeroSection_inclusion, MonObj.comp_one]
  exact congrArg (fun f : T ⟶ p.kernelScheme => f.left) H

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernelInclusion_pow_degree
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i) : p.kernelInclusion ^ ((∏ i, δ i) ^ 2) = 1 := by
  have H := congrArg (fun f : p.kernelScheme ⟶ p.kernelScheme => f ≫ p.kernelInclusion)
    (hp.kernelMultiplication_degree_eq_zero hδ)
  simpa only [Abelian.Schemes.AbelianScheme.Isogeny.kernelMultiplication_inclusion, Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelZeroSection_inclusion,
    MonObj.comp_one] using H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
