import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedComparison
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

/-! # PEL Target Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison

noncomputable section

/-! Equal complete scheme kernels determine the entire independently
specified PEL target. The comparison includes the actual normalized
Poincare bundle, polarization, integral action, and ordered marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Dual OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R] {d N n : ℕ}
variable {A B C : AbelianScheme.TateComparison.PEL.PELFamilyData R d N (Spec (.of k))}
variable (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A C n)
variable (hk : QuotientComparison.SameKernel f.isogeny g.isogeny)

theorem pel_dual_finite : IsFinite f.dualHom.left := by
  rw [PolarizedComparison.pel_dualMap]
  exact Intrinsic.DualIdentification.dualMap_finite A.dual B.dual f.isogeny

theorem quotient_polarization :
    B.polarizationMap.hom = (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom ≫
      C.polarizationMap.hom ≫ DualComparison.dualMap B.dual C.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom := by
  have : IsFinite f.dualHom.left := pel_dual_finite f
  exact PolarizedComparison.quotientIso_preserves_polarization_of_finite_dual f g hk

/-- The dual isomorphism is constructed from Picard pullback. Every
compatibility in this native PEL isomorphism is a proved conclusion. -/
def quotientPELIso : AbelianScheme.TateComparison.PELModuli.PELFamilyIso B C where
  abelian := QuotientComparison.quotientIso f.isogeny g.isogeny hk
  dual := (DualComparison.dualIso B.dual C.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk)).symm
  abelianGroup := inferInstance
  dualGroup := Dual.dualMap_isMonHom C.dual B.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk).inv
  polarization := by
    let e := QuotientComparison.quotientIso f.isogeny g.isogeny hk
    let d := DualComparison.dualIso B.dual C.dual e
    change B.polarizationMap.hom ≫ d.inv = e.hom ≫ C.polarizationMap.hom
    have h : B.polarizationMap.hom = e.hom ≫ C.polarizationMap.hom ≫ d.hom :=
      quotient_polarization f g hk
    rw [h, Category.assoc, Category.assoc, d.hom_inv_id, Category.comp_id]
  poincare := Intrinsic.DualIdentification.dualIso_poincare B.dual C.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk)
  equivariant := PolarizedComparison.quotientIso_preserves_pelAction f g hk
  marking := PolarizedComparison.quotientIso_preserves_pelMarking f g hk

theorem quotientPELIso_projection :
    f.isogeny.hom ≫ (quotientPELIso f g hk).abelian.hom = g.isogeny.hom :=
  QuotientComparison.quotientIso_projection f.isogeny g.isogeny hk

include f g hk in
theorem quotientPELClass_eq :
    (Quotient.mk (AbelianScheme.TateComparison.PELModuli.pelFamilySetoid R d N (Spec (.of k))) B) = Quotient.mk _ C :=
  Quotient.sound ⟨quotientPELIso f g hk⟩

/-- On the positive PEL locus this is an HilbertConstruction isomorphism between the
original polarized families, retaining their supplied positivity proofs. -/
def quotientPolarizedIso {δ : Fin d → ℕ} {c : R →+* R}
    (hB : B.IsPEL δ c) (hC : C.IsPEL δ c) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (B.toPolarized hB) (C.toPolarized hC) where
  abelian := (quotientPELIso f g hk).abelian
  dual := (quotientPELIso f g hk).dual
  abelianGroup := (quotientPELIso f g hk).abelianGroup
  dualGroup := (quotientPELIso f g hk).dualGroup
  polarization := (quotientPELIso f g hk).polarization
  poincare := (quotientPELIso f g hk).poincare
  level := (quotientPELIso f g hk).marking

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison
