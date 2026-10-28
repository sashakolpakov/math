import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceIndices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELKernelTransport

/-! # Quotient Kernel Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuotientKernelTransport.CM

noncomputable section

/-! Full PEL isogeny transport and kernel-choice transport agree,
including proved changes of the arithmetic character and multiplier.
This is an equality of the original subgroup functors on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N s q n n' : ℕ} [Fact q.Prime]
  {A A' B B' : AbelianScheme.TateComparison.PEL.PELFamilyData R g N S}
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B (q ^ n)) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A A') (t : AbelianScheme.TateComparison.PELModuli.PELFamilyIso B B')
  {χ χ' : Fin s → R →+* ℤ_[q]} {a a' : Fin s → Fin 3 → ℕ}
  (hχ : χ = χ') (hn : n = n') (ha : a = a') (H : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ n a)
  (hker : ∀ v, (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock A (χ v) n) = H.val v)

include hker in
theorem splitKernel (v : Fin s) :
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel
      ((f.transport e.symm t).castMultiplier (congrArg (fun m => q ^ m) hn)).isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock A' (χ' v) n') =
    (KernelChoiceIndices.CM.choiceEquiv A' hχ hn ha
      (KernelChoiceTransport.CM.choiceEquiv e χ n a H)).val v := by
  subst χ' n' a'
  exact (AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.splitKernel_transport f e.symm t (χ v) n).trans
    (congrArg (fun J : AbelianScheme.TateComparison.Subgroups.PointSubgroup A.abelian => J.comapHom e.abelian.inv) (hker v))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuotientKernelTransport.CM
