import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharZeroCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Char Zero Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharZeroFibers

noncomputable section

/-! The characteristic-zero structure-sheaf bound holds over every field,
and on any actual cartesian fiber of a projective abelian scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

theorem charZeroAbelian_structureCechH1_finrank_le
    {k : Type} [Field k] [CharZero k] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    {I : Type} [LinearOrder I] [Finite I] (U : I → A.scheme.left.Opens)
    (hU : IsOpenCover U) (haU : ∀ i, IsAffineOpen (U i)) :
    Module.finrank Γ(Spec (.of k), ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.scheme.hom (Line.Bundles.structureModule A.scheme.left) U).sc' 0 1 2).homology ≤ g := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let B := A.pullback b
  let PB := P.baseChange b
  let V := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover B.scheme PB
  have hV : IsOpenCover V := IsOpenCover.mk (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers B.scheme PB)
  have haV := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.affine B.scheme PB
  have h := CharZeroCech.abelian_structureCechH1_finrank_fieldBaseChange A B b
    (pullback.fst A.scheme.hom b) (IsPullback.of_hasPullback A.scheme.hom b)
    U V hU hV haU haV
  exact h.symm.le.trans (CharZeroCech.algClosedCharZeroAbelian_structureCechH1_finrank_le B PB V hV haV)

theorem charZeroAbelian_cartesian_structureCechH1_finrank_le
    {S Y : Scheme} {k : Type} [Field k] [CharZero k] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (b : Spec (.of k) ⟶ S) (f : Y ⟶ A.scheme.left) (ρ : Y ⟶ Spec (.of k))
    (hp : IsPullback f ρ A.scheme.hom b)
    {I : Type} [LinearOrder I] [Finite I] (U : I → Y.Opens)
    (hU : IsOpenCover U) (haU : ∀ i, IsAffineOpen (U i)) :
    Module.finrank Γ(Spec (.of k), ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex ρ (Line.Bundles.structureModule Y) U).sc' 0 1 2).homology ≤ g := by
  let e : Over.mk ρ ≅ (A.pullback b).scheme :=
    Over.isoMk hp.isoPullback hp.isoPullback_hom_snd
  let B := (A.pullback b).transport e.symm
  exact charZeroAbelian_structureCechH1_finrank_le B ((P.baseChange b).ofSourceIso e) U hU haU

theorem charZero_of_rational_scheme_map
    {k : Type} [Field k] (b : Spec (.of k) ⟶ Spec (.of ℚ)) : CharZero k := by
  let c : ℚ →+* k := (Scheme.ΓSpecIso (.of k)).hom.hom.comp
    (b.appTop.hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom)
  let : Algebra ℚ k := c.toAlgebra
  exact Algebra.charZero_of_charZero ℚ k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharZeroFibers
