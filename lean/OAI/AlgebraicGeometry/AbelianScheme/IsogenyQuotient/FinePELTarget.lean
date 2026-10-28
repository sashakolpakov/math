import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Isotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Markings

/-! # Fine PEL Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELTarget.Construction

noncomputable section

/-!
ReferenceFamily's actual fine-moduli property classifies a native PEL family.
An isogeny to that family then has an actual target in the pullback of
the universal family, with its kernel, action, and ordered marking
preserved by the supplied moduli comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel D iota N) (hM : M.IsFine)
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T)

def finePELClassifyingMap : T ⟶ M.space := (hM T A).choose

def finePELClassifyingIso : AbelianModuli.ReferenceFamily.Models.PELPullbackIso M.universal A (finePELClassifyingMap M hM A) :=
  (hM T A).choose_spec.1.some

theorem finePELClassifyingMap_unique (d : T ⟶ M.space)
    (hd : Nonempty (AbelianModuli.ReferenceFamily.Models.PELPullbackIso M.universal A d)) : d = finePELClassifyingMap M hM A :=
  (hM T A).choose_spec.2 d hd

def finePELClassifyingIsogeny {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A.polarized.abelian) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B
      (M.universal.polarized.abelian.pullback (finePELClassifyingMap M hM A).left) := by
  let e := (finePELClassifyingIso M hM A).abelian
  let : IsMonHom e.hom := (finePELClassifyingIso M hM A).abelianGroup
  let : IsIso e.hom.left := (Over.forget T.left).map_isIso e.hom
  exact {
    hom := f.hom ≫ e.hom
    preservesGroup := inferInstance
    finite := inferInstanceAs (IsFinite (f.hom.left ≫ e.hom.left))
    flat := inferInstanceAs (Flat (f.hom.left ≫ e.hom.left))
    surjective := inferInstanceAs (Surjective (f.hom.left ≫ e.hom.left)) }

theorem finePELClassifyingIsogeny_hom {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A.polarized.abelian) :
    (finePELClassifyingIsogeny M hM A f).hom = f.hom ≫ (finePELClassifyingIso M hM A).abelian.hom := rfl

theorem finePELClassifyingIsogeny_etale {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A.polarized.abelian) [Etale f.hom.left] :
    Etale (finePELClassifyingIsogeny M hM A f).hom.left := by
  let e := (finePELClassifyingIso M hM A).abelian
  let : IsIso e.hom.left := (Over.forget T.left).map_isIso e.hom
  exact inferInstanceAs (Etale (f.hom.left ≫ e.hom.left))

theorem finePELClassifyingIsogeny_kernel {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A.polarized.abelian) :
    Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (finePELClassifyingIsogeny M hM A f).hom = Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom := by
  let e := (finePELClassifyingIso M hM A).abelian
  let : IsMonHom e.hom := (finePELClassifyingIso M hM A).abelianGroup
  ext U t x
  change x ≫ (f.hom ≫ e.hom) = 1 ↔ x ≫ f.hom = 1
  rw [← Category.assoc, ← MonObj.one_comp e.hom, cancel_mono]

theorem finePELClassifyingIsogeny_action {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A.polarized.abelian)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (hσ : ∀ a, f.hom ≫ A.action.map a = σ.map a ≫ f.hom)
    (a : NumberField.RingOfIntegers E) :
    (finePELClassifyingIsogeny M hM A f).hom ≫
        (Over.pullback (finePELClassifyingMap M hM A).left).map (M.universal.action.map a) =
      σ.map a ≫ (finePELClassifyingIsogeny M hM A f).hom := by
  let e := (finePELClassifyingIso M hM A).abelian
  let u : (M.universal.polarized.abelian.pullback (finePELClassifyingMap M hM A).left).scheme ⟶
      (M.universal.polarized.abelian.pullback (finePELClassifyingMap M hM A).left).scheme :=
    (Over.pullback (finePELClassifyingMap M hM A).left).map (M.universal.action.map a)
  change (f.hom ≫ e.hom) ≫ u = σ.map a ≫ (f.hom ≫ e.hom)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => f.hom ≫ z) ((finePELClassifyingIso M hM A).action a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ e.hom) (hσ a)).trans (Category.assoc _ _ _))))

theorem finePELClassifyingIsogeny_marking {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A.polarized.abelian) (level : B.FullLevel N)
    (hlevel : ∀ (U : Over T.left)
      (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * s)) → ZMod N))),
      (level.hom.app (.op U) c).val ≫ f.hom = (A.polarized.level.hom.app (.op U) c).val)
    (U : Over T.left) (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * s)) → ZMod N))) :
    (level.hom.app (.op U) c).val ≫ (finePELClassifyingIsogeny M hM A f).hom =
      ((M.universal.polarized.level.pullback (finePELClassifyingMap M hM A).left).hom.app (.op U) c).val := by
  rw [finePELClassifyingIsogeny_hom, ← Category.assoc, hlevel]
  exact (finePELClassifyingIso M hM A).level U c

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELTarget.Construction
