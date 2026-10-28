import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Extension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Polarization Type Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTypeDescent

noncomputable section

/-!
Recover the actual HilbertConstruction polarization type from geometric base changes.
The finite-flat degree is included along with the elementary divisors of
the kernel point groups, so this argument retains scheme-theoretic length.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- A finite flat isogeny's type is detected on its geometric base changes. -/
theorem polarization_type_of_geometric_baseChanges
    {S : Scheme} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (δ : Fin g → ℕ)
    (hfiber : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      (p.pullback s).HasPolarizationType δ) : p.HasPolarizationType δ where
  degree b := by
    let K := AlgebraicClosure (B.scheme.left.residueField b)
    let a := Spec.map (CommRingCat.ofHom (algebraMap (B.scheme.left.residueField b) K)) ≫
      B.scheme.left.fromSpecResidueField b
    let s := a ≫ B.scheme.hom
    let k : Spec (.of K) := IsLocalRing.closedPoint K
    have hak : a k = b := B.scheme.left.fromSpecResidueField_apply b _
    have hbk : B.scheme.hom b = s k := by
      change B.scheme.hom b = B.scheme.hom (a k)
      rw [hak]
    obtain ⟨z, hzb, _⟩ := Scheme.Pullback.exists_preimage_pullback b k hbk
    have h := Scheme.Hom.finrank_of_isPullback _ _ _ _
      (ArithmeticGeometry.OrdinaryLocus.Openness.RelativeBaseChange.Construction.isPullback_overPullback_map p.hom s) z
    exact (congrArg p.hom.left.finrank hzb).symm.trans
      (h.symm.trans ((hfiber K s).degree z))
  geometricKernel K _ _ s := by
    obtain ⟨e⟩ := (hfiber K s).geometricKernel K (𝟙 _)
    let c := p.kernelBaseChangeEquiv s (Over.mk (𝟙 (Spec (.of K))))
    have he := c.symm.trans e
    have hobj : (Over.map s).obj (Over.mk (𝟙 (Spec (.of K)))) = Over.mk s := by
      change Over.mk ((𝟙 _) ≫ s) = Over.mk s
      rw [Category.id_comp]
    exact hobj ▸ Nonempty.intro he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTypeDescent
