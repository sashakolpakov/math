import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenKernelTargets
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Isogeny.FiberExtension
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers

/-! # Chosen Branch Targets -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ChosenBranchTargets.CM.FieldKernel

/-! Chosen-kernel target uniqueness holds over the original evaluation
field. Extend the actual isogenies and kernels to its algebraic closure,
apply geometric uniqueness, and descend the equality of moduli points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  {k : Type} [Field k] {b : Spec (.of k) ⟶ Spec (.of K)} {m : ℕ}
  (x y z : D.GeometricPoint b)
  (e : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ m))
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b z) (q ^ m))
  (hker : ∀ v : Fin s,
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel e.isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) m) =
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) m))

include hg hgeometry hdegree hs hker in
theorem target_eq : y = z := by
  let σ := algebraMap k (AlgebraicClosure k)
  let ee := Isogeny.FiberExtension.CM.isogeny D σ b x y e
  let ff := Isogeny.FiberExtension.CM.isogeny D σ b x z f
  have he : FieldPointDescent.CM.testMap σ b ≫ y = FieldPointDescent.CM.testMap σ b ≫ z := by
    apply ChosenKernelTargets.CM.target_eq D hg hgeometry (FieldPointDescent.CM.testMap σ b ≫ x)
      (FieldPointDescent.CM.testMap σ b ≫ y) (FieldPointDescent.CM.testMap σ b ≫ z) ee ff _ hdegree hs
    intro v
    rw [Isogeny.FiberExtension.CM.splitKernel, Isogeny.FiberExtension.CM.splitKernel, hker v]
  exact (cancel_epi (FieldPointDescent.CM.testMap σ b)).mp he

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ChosenBranchTargets.CM.FieldKernel

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ChosenBranchTargets.CM

/-! A quotient with the chosen kernels indexed by a IsogenyQuotient branch has
that branch's actual moduli target. All-test chosen-kernel comparison,
full polarization and fine moduli uniqueness prove the identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (t : AbelianScheme.TateComparison.Local.IntegralType s)
  {k : Type} [Field k] {b : Spec (.of k) ⟶ Spec (.of K)} (x : D.GeometricPoint b)
  {I : Type*} (e : I ≃ D.chosenKernels t x)

def branchEquiv : I ≃ (D.correspondence t).Fiber x :=
  e.trans (D.c46FiberKernelEquiv hIsogenyQuotient t x).symm

def branchIsogeny (a : I) : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x)
    (D.fiberFamily b ((D.correspondence t).endpoint (branchEquiv D hIsogenyQuotient t x e a)))
    (q ^ t.multiplierNat) :=
  D.c46FiberIsogeny hIsogenyQuotient t x _ (branchEquiv D hIsogenyQuotient t x e a).val
    (branchEquiv D hIsogenyQuotient t x e a).property rfl

theorem branchIsogeny_kernel (a : I) (v : Fin s) :
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (branchIsogeny D hIsogenyQuotient t x e a).isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) t.multiplierNat) =
        (e a).val v := by
  have h := D.c46FiberIsogeny_kernel hIsogenyQuotient t x _ (branchEquiv D hIsogenyQuotient t x e a).val
    (branchEquiv D hIsogenyQuotient t x e a).property rfl v
  exact h.trans (congrArg (fun J : D.chosenKernels t x => J.val v)
    ((D.c46FiberKernelEquiv hIsogenyQuotient t x).apply_symm_apply (e a)))

include hg hgeometry hdegree hs in
theorem target_eq (a : I) (y : D.GeometricPoint b)
    (Q : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ t.multiplierNat))
    (hQ : ∀ v : Fin s, (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel Q.isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) t.multiplierNat) = (e a).val v) :
    y = (D.correspondence t).endpoint (branchEquiv D hIsogenyQuotient t x e a) :=
  FieldKernel.target_eq D hg hgeometry hdegree hs x y _ Q
    (branchIsogeny D hIsogenyQuotient t x e a)
    (fun v => (hQ v).trans (branchIsogeny_kernel D hIsogenyQuotient t x e a v).symm)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ChosenBranchTargets.CM

end

end OAI
