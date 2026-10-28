import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Base change of isomorphisms and isomorphism classes in the polarized level moduli problem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {S S' : Scheme.{u}}

/-- The chosen ordered torsion basis pulls back to the same basis on test-scheme points. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.pullback_basis {A : Abelian.Schemes.AbelianScheme g S} (level : A.FullLevel N)
    (f : S' ⟶ S) (T : Over S')
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.baseChangePointsEquiv f T ((level.pullback f).hom.app (.op T) c).val =
      (level.hom.app (.op ((Over.map f).obj T)) c).val :=
  congrArg (fun x : A.torsionPoints N ((Over.map f).obj T) => x.val)
    ((A.torsionBaseChangeEquiv f T N).apply_symm_apply
      (level.hom.app (.op ((Over.map f).obj T)) c))

/-- The product map used to pull back Poincare bundles is natural in both factors. -/
theorem Moduli.BaseChange.poincarePullbackOverMap_naturality {A B : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (E : Dual.Data.DualAbelianData B)
    (u : D.abelian.scheme ⟶ E.abelian.scheme) (v : A.scheme ⟶ B.scheme) (f : S' ⟶ S) :
    ((Over.pullback f).map u ⊗ₘ (Over.pullback f).map v).left ≫
        (E.poincarePullbackOverMap f).left =
      (D.poincarePullbackOverMap f).left ≫ (u ⊗ₘ v).left := by
  let A₁ := (A.pullback f).scheme
  let B₁ := (B.pullback f).scheme
  let D₁ := (D.abelian.pullback f).scheme
  let E₁ := (E.abelian.pullback f).scheme
  let q : (D₁ ⊗ A₁).left ⟶ (E₁ ⊗ B₁).left :=
    ((Over.pullback f).map u ⊗ₘ (Over.pullback f).map v).left
  let r : (E₁ ⊗ B₁).left ⟶ (E.abelian.scheme ⊗ B.scheme).left :=
    (E.poincarePullbackOverMap f).left
  let a : (D₁ ⊗ A₁).left ⟶ (D.abelian.scheme ⊗ A.scheme).left :=
    (D.poincarePullbackOverMap f).left
  let b : (D.abelian.scheme ⊗ A.scheme).left ⟶ (E.abelian.scheme ⊗ B.scheme).left := (u ⊗ₘ v).left
  change q ≫ r = a ≫ b
  apply Over.tensorObj_ext
  · have hq : q ≫ pullback.fst E₁.hom B₁.hom =
        pullback.fst D₁.hom A₁.hom ≫ ((Over.pullback f).map u).left :=
      Over.tensorHom_left_fst _ _ _ _
    have hr : r ≫ pullback.fst E.abelian.scheme.hom B.scheme.hom =
        pullback.fst E₁.hom B₁.hom ≫ pullback.fst E.abelian.scheme.hom f :=
      E.poincarePullbackOverMap_left_fst f
    have ha : a ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst D₁.hom A₁.hom ≫ pullback.fst D.abelian.scheme.hom f :=
      D.poincarePullbackOverMap_left_fst f
    have hb : b ≫ pullback.fst E.abelian.scheme.hom B.scheme.hom =
        pullback.fst D.abelian.scheme.hom A.scheme.hom ≫ u.left := Over.tensorHom_left_fst _ _ _ _
    exact (Category.assoc q r _).trans
      ((congrArg (fun z => q ≫ z) hr).trans
        (((Category.assoc q _ _).symm.trans
          (congrArg (fun z => z ≫ pullback.fst E.abelian.scheme.hom f) hq)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => pullback.fst D₁.hom A₁.hom ≫ z)
              (Pullback.Comparisons.overPullback_map_left_fst u f)).trans
              (((Category.assoc _ _ _).symm.trans
                (congrArg (fun z => z ≫ u.left) ha.symm)).trans
                ((Category.assoc a _ _).trans
                  ((congrArg (fun z => a ≫ z) hb.symm).trans
                    (Category.assoc a b _).symm)))))))
  · have hq : q ≫ pullback.snd E₁.hom B₁.hom =
        pullback.snd D₁.hom A₁.hom ≫ ((Over.pullback f).map v).left :=
      Over.tensorHom_left_snd _ _ _ _
    have hr : r ≫ pullback.snd E.abelian.scheme.hom B.scheme.hom =
        pullback.snd E₁.hom B₁.hom ≫ pullback.fst B.scheme.hom f :=
      E.poincarePullbackOverMap_left_snd f
    have ha : a ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd D₁.hom A₁.hom ≫ pullback.fst A.scheme.hom f :=
      D.poincarePullbackOverMap_left_snd f
    have hb : b ≫ pullback.snd E.abelian.scheme.hom B.scheme.hom =
        pullback.snd D.abelian.scheme.hom A.scheme.hom ≫ v.left := Over.tensorHom_left_snd _ _ _ _
    exact (Category.assoc q r _).trans
      ((congrArg (fun z => q ≫ z) hr).trans
        (((Category.assoc q _ _).symm.trans
          (congrArg (fun z => z ≫ pullback.fst B.scheme.hom f) hq)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => pullback.snd D₁.hom A₁.hom ≫ z)
              (Pullback.Comparisons.overPullback_map_left_fst v f)).trans
              (((Category.assoc _ _ _).symm.trans
                (congrArg (fun z => z ≫ v.left) ha.symm)).trans
                ((Category.assoc a _ _).trans
                  ((congrArg (fun z => a ≫ z) hb.symm).trans
                    (Category.assoc a b _).symm)))))))

/-- Polarization- and level-preserving isomorphisms pull back. -/
def Moduli.Isomorphisms.LevelPreservingIso.pullback {δ : Fin g → ℕ}
    {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (e : Moduli.Isomorphisms.LevelPreservingIso A B) (f : S' ⟶ S) :
    Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (B.pullback f) where
  abelian := (Over.pullback f).mapIso e.abelian
  dual := (Over.pullback f).mapIso e.dual
  abelianGroup := inferInstanceAs (IsMonHom ((Over.pullback f).map e.abelian.hom))
  dualGroup := inferInstanceAs (IsMonHom ((Over.pullback f).map e.dual.hom))
  polarization := ((Over.pullback f).map_comp A.polarization.isogeny.hom e.dual.hom).symm.trans
    ((congrArg (fun h => (Over.pullback f).map h) e.polarization).trans
      ((Over.pullback f).map_comp e.abelian.hom B.polarization.isogeny.hom))
  poincare :=
    (Line.Bundles.LineBundle.pullbackClass_comp
      ((Over.pullback f).map e.dual.hom ⊗ₘ (Over.pullback f).map e.abelian.hom).left
      (B.dual.poincarePullbackOverMap f).left (Line.Bundles.LineBundle.classOf B.dual.poincare)).symm.trans
        ((congrArg (fun h => Line.Bundles.LineBundle.pullbackClass h (Line.Bundles.LineBundle.classOf B.dual.poincare))
          (Moduli.BaseChange.poincarePullbackOverMap_naturality A.dual B.dual e.dual.hom e.abelian.hom f)).trans
          ((Line.Bundles.LineBundle.pullbackClass_comp (A.dual.poincarePullbackOverMap f).left
            (e.dual.hom ⊗ₘ e.abelian.hom).left (Line.Bundles.LineBundle.classOf B.dual.poincare)).trans
            (congrArg (Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap f).left) e.poincare)))
  level T c := by
    apply (B.abelian.baseChangePointsEquiv f T).injective
    exact (Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map e.abelian.hom f T
      ((A.level.pullback f).hom.app (.op T) c).val).trans
        ((congrArg (fun h => h ≫ e.abelian.hom) (A.level.pullback_basis f T c)).trans
          ((e.level ((Over.map f).obj T) c).trans (B.level.pullback_basis f T c).symm))

/-- Pullback is well-defined on isomorphism classes of polarized full-level data. -/
def Moduli.Isomorphisms.PolarizedLevelClasses.pullback {δ : Fin g → ℕ} (f : S' ⟶ S) :
    Moduli.Isomorphisms.PolarizedLevelClasses g δ N S → Moduli.Isomorphisms.PolarizedLevelClasses g δ N S' :=
  Quotient.map (fun A => A.pullback f) (fun _ _ ⟨e⟩ => ⟨e.pullback f⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
