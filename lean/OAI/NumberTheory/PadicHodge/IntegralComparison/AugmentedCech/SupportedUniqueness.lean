import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.LiftUniqueness
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalKernelHomRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForget

/-! # Supported Uniqueness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.SupportedUniqueness

noncomputable section

/-! The actual augmented ordered Čech support map admits a unique lift
up to homotopy from a complex with exact Hom rows on positive columns. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForget
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D]
  (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) [(AugmentedOrdered.CechFunctor.bicomplex U K).HasTotal (.up ℕ)]
  (S : CochainComplex D ℕ)
  (hK : ∀ p q, q ≠ 0 → Cochain.HomAcyclic.Rows S (((AugmentedOrdered.CechFunctor.bicomplex U K).X p).X q))

include hK in
theorem kernel_rows (n : ℕ) : Cochain.HomAcyclic.Rows S ((kernel (AugmentedOrdered.CechForget.forgetSupport U K)).X n) := by
  let e := PreservesKernel.iso (HomologicalComplex.eval D (.up ℕ) n) (AugmentedOrdered.CechForget.forgetSupport U K)
  let e' := kernelCompMono ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (AugmentedOrdered.CechFunctor.bicomplex U K)) n 0 n) (AugmentedOrdered.CechZero.zeroIso U (K.X n)).hom
  exact Cochain.HomAcyclicProducts.rows_retract (TotalKernelHomRows.rows (AugmentedOrdered.CechFunctor.bicomplex U K) n S hK)
    (e.hom ≫ e'.hom) (e'.inv ≫ e.inv) (by simp)

def degreeSection (n : ℕ) : (AugmentedOrdered.CechForget.ambientComplex K).X n ⟶ ((AugmentedOrdered.CechFunctor.bicomplex U K).total (.up ℕ)).X n :=
  (AugmentedOrdered.CechZero.zeroIso U (K.X n)).inv ≫ (AugmentedOrdered.CechFunctor.bicomplex U K).ιTotal (.up ℕ) n 0 n (by change n + 0 = n; omega)

theorem section_projection (n : ℕ) : degreeSection U K n ≫ (AugmentedOrdered.CechForget.forgetSupport U K).f n = 𝟙 _ := by
  simp [degreeSection, AugmentedOrdered.CechForget.forgetSupport]

def homotopy (f g : S ⟶ (AugmentedOrdered.CechFunctor.bicomplex U K).total (.up ℕ))
    (h : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U K) (g ≫ AugmentedOrdered.CechForget.forgetSupport U K)) : Homotopy f g :=
  Supported.LiftUniqueness.of_comp_homotopy (AugmentedOrdered.CechForget.forgetSupport U K)
    (kernel_rows U K S hK) (degreeSection U K) (section_projection U K) f g h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.SupportedUniqueness
