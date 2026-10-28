import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointFieldPairing
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationPointComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CoprimeTorsionIs
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap

/-! # Poincare Bundle Torsion Point -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PoincareBundleTorsionPoint.Construction

noncomputable section

section

/-! The PoincareBundle pullback kernel and the original multiplication equalizer
carry the same torsion points and the same included dual torsion points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ) (T : Over (Spec (.of k)))
  (x : (A.abelian.torsionFunctor n).obj (.op T))

theorem originalPointToFieldNative_equalizer :
    ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x ≫ (Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.abelian.scheme) ^ n)).inv =
      IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.abelian.scheme) ^ n)) :=
    inferInstanceAs (Mono (equalizer.ι ((𝟙 A.abelian.scheme) ^ n) 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.abelian.scheme) ^ n))).mp
  let e := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.abelian.scheme) ^ n)
  have hi : e.inv ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.abelian.scheme) ^ n) =
      Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A.abelian.scheme) ^ n) :=
    (congrArg (fun f => e.inv ≫ f) (Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso_inclusion ((𝟙 A.abelian.scheme) ^ n)).symm).trans
      (e.inv_hom_id_assoc _)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x ≫ f) hi).trans
      ((IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.abelian.scheme n x.val x.property).trans
        (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint_inclusion A.abelian n T x).symm))

variable {D : Over (Spec (.of k))} [GrpObj D] [IsCommMonObj D]
  (φ : A.abelian.scheme ⟶ D) [IsMonHom φ]
  (hφ : (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A.abelian.scheme) ^ n) ≫ φ) ^ n = 1)

theorem originalPointToFieldNative_dualTorsion :
    ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x ≫ TorsionQuotient.SubgroupFunctor.torsionLift n
      (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A.abelian.scheme) ^ n) ≫ φ) hφ =
    IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap φ n := by
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι D n) := inferInstanceAs (Mono (equalizer.ι ((𝟙 D) ^ n) 1))
  apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι D n)).mp
  have hl : (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x ≫ TorsionQuotient.SubgroupFunctor.torsionLift n
      (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A.abelian.scheme) ^ n) ≫ φ) hφ) ≫ TorsionQuotient.SubgroupFunctor.torsionι D n = x.val ≫ φ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x ≫ f) (TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ φ) (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.abelian.scheme n x.val x.property))))
  have hr : (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap φ n) ≫
      TorsionQuotient.SubgroupFunctor.torsionι D n = x.val ≫ φ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T x ≫ f)
        (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion φ n)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ φ) (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint_inclusion A.abelian n T x))))
  exact hl.trans hr.symm

end

section

/-! Every PoincareBundle native torsion point corresponds to its actual original
HilbertConstruction torsion point, naturally under all changes of test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ)

def fieldNativePointToOriginal (T : Over (Spec (.of k)))
    (z : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n) :
    (A.abelian.torsionFunctor n).obj (.op T) :=
  ⟨z ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n,
    (MonObj.comp_pow _ n z).symm.trans
      ((congrArg (fun f => z ≫ f) (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion_killed A.abelian.scheme n)).trans
        (MonObj.comp_one z))⟩

theorem fieldNativePointToOriginal_toNative (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor n).obj (.op T)) :
    fieldNativePointToOriginal A n T (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x) = x :=
  Subtype.ext (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.abelian.scheme n x.val x.property)

theorem originalPointToFieldNative_toOriginal (T : Over (Spec (.of k)))
    (z : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n) :
    ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T (fieldNativePointToOriginal A n T z) = z := by
  apply (cancel_mono (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n)).mp
  exact IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.abelian.scheme n
    (fieldNativePointToOriginal A n T z).val (fieldNativePointToOriginal A n T z).property

def fieldNativeTorsionPointsEquiv (T : Over (Spec (.of k))) :
    (T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n) ≃
      (A.abelian.torsionFunctor n).obj (.op T) where
  toFun := fieldNativePointToOriginal A n T
  invFun := ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T
  left_inv := originalPointToFieldNative_toOriginal A n T
  right_inv := fieldNativePointToOriginal_toNative A n T

theorem fieldNativePointToOriginal_natural {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (z : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n) :
    fieldNativePointToOriginal A n U (t ≫ z) =
      (A.abelian.torsionFunctor n).map t.op (fieldNativePointToOriginal A n T z) :=
  Subtype.ext (Category.assoc t z (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n))

end

/-! The actual PoincareBundle quotient kernel and its torsion inclusion retain
precisely the original included points and their all-test lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ) {B : Over (Spec (.of k))} [GrpObj B]
  (f : A.abelian.scheme ⟶ B) [IsMonHom f]
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.abelian.scheme), x ≫ f = 1 → x ^ n = 1)

def e45KernelTorsionPoint (T : Over (Spec (.of k))) (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :
    (A.abelian.torsionFunctor n).obj (.op T) :=
  fieldNativePointToOriginal A n T (z ≫ Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf)

theorem e45KernelTorsionPoint_val (T : Over (Spec (.of k))) (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :
    (e45KernelTorsionPoint A n f hf T z).val = z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f :=
  (Category.assoc z (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf)
    (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((𝟙 A.abelian.scheme) ^ n))).trans
      (congrArg (fun i => z ≫ i) (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap_inclusion f n hf))

theorem e45KernelTorsionPoint_killed (T : Over (Spec (.of k))) (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :
    (e45KernelTorsionPoint A n f hf T z).val ≫ f = 1 :=
  (congrArg (fun x => x ≫ f) (e45KernelTorsionPoint_val A n f hf T z)).trans
    (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f T z).property

def originalPointToPoincareBundleKernel (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor n).obj (.op T)) (hx : x.val ≫ f = 1) :
    T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f :=
  (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f T).symm ⟨x.val, hx⟩

theorem e45KernelTorsionPoint_lift (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor n).obj (.op T)) (hx : x.val ≫ f = 1) :
    e45KernelTorsionPoint A n f hf T (originalPointToPoincareBundleKernel A n f T x hx) = x := by
  apply Subtype.ext
  exact (e45KernelTorsionPoint_val A n f hf T (originalPointToPoincareBundleKernel A n f T x hx)).trans
    (CategoryTheory.Limits.pullback.lift_fst _ _ _)

theorem originalPointToPoincareBundleKernel_torsionMap (T : Over (Spec (.of k)))
    (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n)
    (hy : (fieldNativePointToOriginal A n T y).val ≫ f = 1) :
    originalPointToPoincareBundleKernel A n f T (fieldNativePointToOriginal A n T y) hy ≫
      Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf = y := by
  apply (fieldNativeTorsionPointsEquiv A n T).injective
  exact e45KernelTorsionPoint_lift A n f hf T (fieldNativePointToOriginal A n T y) hy

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PoincareBundleTorsionPoint.Construction
