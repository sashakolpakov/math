import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELTarget
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceTransport

/-! # Fine PEL Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELPolarization.Construction

noncomputable section

section

/-!
The actual fine-moduli comparison identifies its inverse dual with the
canonical Picard pullback. Transporting an isogeny to the universal
target preserves the full polarization pullback, over arbitrary bases.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceTransport.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel D iota N) (hM : M.IsFine)
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T)

def finePELClassifyingLevelIso : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.polarized
    (M.universal.polarized.pullback (FinePELTarget.Construction.finePELClassifyingMap M hM A).left) :=
  (FinePELTarget.Construction.finePELClassifyingIso M hM A).toPELIso.polarized

theorem finePELClassifyingIso_dual_native :
    (FinePELTarget.Construction.finePELClassifyingIso M hM A).dual.inv =
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (finePELClassifyingLevelIso M hM A).abelian.hom
        A.polarized.dual (M.universal.polarized.dual.pullback (FinePELTarget.Construction.finePELClassifyingMap M hM A).left) :=
  FrobeniusKernel.SourceTransport.Construction.levelIso_dual_inv_eq_native (finePELClassifyingLevelIso M hM A)

theorem finePELClassifyingIsogeny_polarization_pullback
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left} (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A.polarized.abelian) :
    FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom (FinePELTarget.Construction.finePELClassifyingIsogeny M hM A f).hom DB
        (M.universal.polarized.dual.pullback (FinePELTarget.Construction.finePELClassifyingMap M hM A).left)
        (M.universal.polarized.polarization.pullback (FinePELTarget.Construction.finePELClassifyingMap M hM A).left) =
      FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom DB A.polarized.dual A.polarized.polarization := by
  let e := finePELClassifyingLevelIso M hM A
  have h := FrobeniusKernel.SourceTransport.Construction.polarizationPullbackHom_composition f.hom e.abelian.hom DB A.polarized.dual
    (M.universal.polarized.dual.pullback (FinePELTarget.Construction.finePELClassifyingMap M hM A).left)
    (M.universal.polarized.polarization.pullback (FinePELTarget.Construction.finePELClassifyingMap M hM A).left)
  exact h.trans (congrArg
    (fun z => f.hom ≫ z ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DB A.polarized.dual)
    (FrobeniusKernel.SourceTransport.Construction.levelIso_polarization_pullback e))

end

/-! Fine classification respects complete PEL isomorphisms and
arbitrary base change. The equalities are of actual moduli maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
  {T U : Over (Spec (.of K))}

theorem finePELClassifyingMap_eq_of_iso {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T}
    (e : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso A B) : FinePELTarget.Construction.finePELClassifyingMap M hM A = FinePELTarget.Construction.finePELClassifyingMap M hM B := by
  apply FinePELTarget.Construction.finePELClassifyingMap_unique M hM B
  exact ⟨AbelianModuli.ReferenceFamily.Models.PELPullbackIso.ofPELIso (e.symm.trans (FinePELTarget.Construction.finePELClassifyingIso M hM A).toPELIso)⟩

include hM in
theorem finePELMaps_eq_of_pullback_iso (a b : T ⟶ M.space)
    (e : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso (M.universal.pullback a) (M.universal.pullback b)) : a = b :=
  (FinePELTarget.Construction.finePELClassifyingMap_unique M hM (M.universal.pullback b) a
    ⟨AbelianModuli.ReferenceFamily.Models.PELPullbackIso.ofPELIso e.symm⟩).trans
      (FinePELTarget.Construction.finePELClassifyingMap_unique M hM (M.universal.pullback b) b
        ⟨AbelianModuli.ReferenceFamily.Models.PELPullbackIso.canonical M.universal b⟩).symm

theorem finePELClassifyingMap_pullback (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T) (b : U ⟶ T) :
    FinePELTarget.Construction.finePELClassifyingMap M hM (A.pullback b) = b ≫ FinePELTarget.Construction.finePELClassifyingMap M hM A := by
  symm
  apply FinePELTarget.Construction.finePELClassifyingMap_unique M hM (A.pullback b)
  exact ⟨AbelianModuli.ReferenceFamily.Models.PELPullbackIso.ofPELIso
    (((FinePELTarget.Construction.finePELClassifyingIso M hM A).toPELIso.pullback b).trans
      (AbelianModuli.ReferenceFamily.PEL.Objects.PELIso.pullbackComp M.universal (FinePELTarget.Construction.finePELClassifyingMap M hM A) b).symm)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELPolarization.Construction
