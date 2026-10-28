import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PoincareBundleTorsionPoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleCanonicalWeilValue

/-! # Bundle Self Annihilator Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleSelfAnnihilatorTransport.Construction

noncomputable section

/-! Exact all-test kernel realization and original canonical
self-annihilation supply PoincareBundle's actual kernel-scheme hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ) (hn : 0 < n) {B : Over (Spec (.of k))} [GrpObj B]
  (f : A.abelian.scheme ⟶ B) [IsMonHom f]
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.abelian.scheme), x ≫ f = 1 → x ^ n = 1)
  (P : ∀ (T : Over (Spec (.of k))), (T ⟶ A.abelian.scheme) → Prop)
  (hP : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.abelian.scheme), x ≫ f = 1 ↔ P T x)
  (hann : ∀ (T : Over (Spec (.of k))) (y : (A.abelian.torsionFunctor n).obj (.op T)),
    (∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (x : (A.abelian.torsionFunctor n).obj (.op U)),
      P U x.val → Prescription.Construction.canonicalTorsionOrthogonal A n hn U x ((A.abelian.torsionFunctor n).map t.op y)) ↔ P T y.val)

include hP hann in
theorem e45SelfAnnihilating_of_original :
    Picard.PoincareBundle.Canonical.WeilData.SelfAnnihilating A.dual A.polarization.isogeny n hn
      (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf) := by
  intro T y
  constructor
  · intro hy
    have hyo : P T (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal A n T y).val := by
      apply (hann T (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal A n T y)).mp
      intro U t x hx
      have hxk := (hP U x.val).mpr hx
      let z := PoincareBundleTorsionPoint.Construction.originalPointToPoincareBundleKernel A n f U x hxk
      have hz := (BundleCanonicalWeilValue.Construction.e45CanonicalWeilValue_eq_one_iff_native A n hn U
        (z ≫ Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf) (t ≫ y)).mp (hy U t z)
      exact (congrArg₂ (Prescription.Construction.canonicalTorsionOrthogonal A n hn U)
        (PoincareBundleTorsionPoint.Construction.e45KernelTorsionPoint_lift A n f hf U x hxk)
        (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal_natural A n t y)).mp hz
    exact ⟨PoincareBundleTorsionPoint.Construction.originalPointToPoincareBundleKernel A n f T (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal A n T y) ((hP T _).mpr hyo),
      PoincareBundleTorsionPoint.Construction.originalPointToPoincareBundleKernel_torsionMap A n f hf T y ((hP T _).mpr hyo)⟩
  · rintro ⟨z, rfl⟩ U t w
    have hzy := (hP T (PoincareBundleTorsionPoint.Construction.e45KernelTorsionPoint A n f hf T z).val).mp
      (PoincareBundleTorsionPoint.Construction.e45KernelTorsionPoint_killed A n f hf T z)
    have hwx := (hP U (PoincareBundleTorsionPoint.Construction.e45KernelTorsionPoint A n f hf U w).val).mp
      (PoincareBundleTorsionPoint.Construction.e45KernelTorsionPoint_killed A n f hf U w)
    have horth := ((hann T (PoincareBundleTorsionPoint.Construction.e45KernelTorsionPoint A n f hf T z)).mpr hzy) U t
      (PoincareBundleTorsionPoint.Construction.e45KernelTorsionPoint A n f hf U w) hwx
    apply (BundleCanonicalWeilValue.Construction.e45CanonicalWeilValue_eq_one_iff_native A n hn U
      (w ≫ Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf)
      (t ≫ (z ≫ Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf))).mpr
    exact (congrArg (fun y' => Prescription.Construction.canonicalTorsionOrthogonal A n hn U
      (PoincareBundleTorsionPoint.Construction.e45KernelTorsionPoint A n f hf U w) y')
      (PoincareBundleTorsionPoint.Construction.fieldNativePointToOriginal_natural A n t (z ≫ Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf))).mpr horth

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleSelfAnnihilatorTransport.Construction
