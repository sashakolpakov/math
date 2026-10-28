import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELTarget
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Specialization
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices

/-! # Tate Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateTransport.Construction

noncomputable section

/-!
Canonical comparisons of actual quotient schemes preserve the entire
Tate preimage. This applies to universal quotient fibers and to transport
into the universal PEL family, so their raw block lattices are unchanged.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

universe u

theorem isogenyTatePreimage_postcompose_iso
    {S : Scheme.{u}} {A B C : Over S}
    [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
    (T : Over S) (q : ℕ) [Fact q.Prime]
    (f : A ⟶ B) [IsMonHom f] (e : B ≅ C) [IsMonHom e.hom] :
    TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) (f ≫ e.hom) =
      TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) f := by
  apply le_antisymm
  · have h := TateComparison.Lattices.isogenyTatePreimage_mono_comp T q (f ≫ e.hom) e.inv
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using h
  · exact TateComparison.Lattices.isogenyTatePreimage_mono_comp T q f e.hom

theorem isogenyTatePreimage_same_kernel
    {S : Scheme.{u}} {d : ℕ} {A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S}
    (T : Over S) (q : ℕ) [Fact q.Prime]
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (hker : Isogenies.NeighborCounting.QuotientComparison.SameKernel f g) :
    TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) f.hom =
      TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) g.hom := by
  have h := isogenyTatePreimage_postcompose_iso T q f.hom (Isogenies.NeighborCounting.QuotientComparison.quotientIso f g hker)
  simpa only [Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection] using h.symm

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel D iota N) (hM : M.IsFine)
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T)

theorem finePELClassifyingIsogeny_tate_preimage
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A.polarized.abelian)
    (U : Over T.left) (q : ℕ) [Fact q.Prime] :
    TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) (FinePELTarget.Construction.finePELClassifyingIsogeny M hM A f).hom =
      TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) f.hom := by
  let e := (FinePELTarget.Construction.finePELClassifyingIso M hM A).abelian
  let : IsMonHom e.hom := (FinePELTarget.Construction.finePELClassifyingIso M hM A).abelianGroup
  exact isogenyTatePreimage_postcompose_iso U q f.hom e

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateTransport.Construction
