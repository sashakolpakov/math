import OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.BeckDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantComparison
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Iso Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IsoDescent

noncomputable section

/-!
# Invariant sheaves under isomorphisms of schemes

These constructions transport geometric descent to affine coordinate
spectra without changing the line bundles or their coaction equations.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

universe u

variable {X Y X' Y' : Scheme.{u}}

/-- Pullback along a scheme isomorphism is an equivalence of module-sheaf categories. -/
def pullbackEquivalence (e : X' ≅ X) : X.Modules ≌ X'.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    (Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId X).symm
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X')

theorem pullback_isEquivalence (e : X' ≅ X) :
    (Scheme.Modules.pullback e.hom).IsEquivalence :=
  (pullbackEquivalence e).isEquivalence_functor

/-- Local rank one is detected after changing the scheme by an isomorphism. -/
theorem isLine_of_pullback (e : X' ≅ X) (M : X.Modules)
    (h : Line.Bundles.IsLine ((Scheme.Modules.pullback e.hom).obj M)) :
    Line.Bundles.IsLine M := by
  let a : (Scheme.Modules.pullback e.inv).obj
      ((Scheme.Modules.pullback e.hom).obj M) ≅ M :=
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId X).app M)
  exact (h.pullback e.inv).of_iso a

variable (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ≅ X) (j : Y' ≅ Y)
  (w : g ≫ j.hom = i.hom ≫ f)

/-- The two composed direct images in an isomorphic square agree. -/
def pushforwardSquareIso :
    Scheme.Modules.pushforward i.hom ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward j.hom :=
  Scheme.Modules.pushforwardComp i.hom f ≪≫
    Scheme.Modules.pushforwardCongr w.symm ≪≫ (Scheme.Modules.pushforwardComp g j.hom).symm

/-- The corresponding commutative square of pullback functors. -/
def pullbackSquareIso :
    Scheme.Modules.pullback j.hom ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback i.hom :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction i.hom))
    ((Scheme.Modules.pullbackPushforwardAdjunction j.hom).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))).symm
    (pushforwardSquareIso f g i j w)

/-- Direct-image base change along the vertical scheme isomorphisms. -/
def baseChangeMap :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback j.hom ⟶
      Scheme.Modules.pullback i.hom ⋙ Scheme.Modules.pushforward g :=
  ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction i.hom)
    (Scheme.Modules.pullbackPushforwardAdjunction j.hom)).symm
      (TwoSquare.mk _ _ _ _ (pushforwardSquareIso f g i j w).hom)).natTrans

theorem baseChangeMap_isIso : IsIso (baseChangeMap f g i j w) := by
  have := pullback_isEquivalence i
  have := pullback_isEquivalence j
  dsimp [baseChangeMap, mateEquiv]
  infer_instance

/-- The canonical adjunction mate is the invertible base-change map. -/
theorem rightMate_eq :
    DescentRestriction.rightMate
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (pullbackSquareIso f g i j w) = baseChangeMap f g i j w := by
  let γ := TwoSquare.mk _ _ _ _ (pushforwardSquareIso f g i j w).hom
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction j.hom)
    (Scheme.Modules.pullbackPushforwardAdjunction i.hom) γ
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction g)).symm.injective
  change (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction g)).symm
      ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction g))
          (TwoSquare.mk _ _ _ _ (pullbackSquareIso f g i j w).hom)) = _
  rw [Equiv.symm_apply_apply]
  exact h.symm

/-- Full geometric coactions transport through an isomorphic scheme square. -/
def transportDatum : BeckDescent.SheafDatum f ⥤ BeckDescent.SheafDatum g :=
  DescentRestriction.coalgebraRestriction
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction g) (pullbackSquareIso f g i j w)

/-- Taking invariants commutes with this change of schemes. -/
def invariantSheafIso (D : BeckDescent.SheafDatum f) :
    (Scheme.Modules.pullback j.hom).obj (BeckDescent.invariantSheaf f D) ≅
      BeckDescent.invariantSheaf g ((transportDatum f g i j w).obj D) := by
  have := pullback_isEquivalence j
  have : IsIso (DescentRestriction.rightMate
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g) (pullbackSquareIso f g i j w)) := by
    rw [rightMate_eq]
    exact baseChangeMap_isIso f g i j w
  exact InvariantRestriction.invariantRestrictionIso
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction g) (pullbackSquareIso f g i j w) D

/-- Isomorphism of the canonical pullback comparison is detected after
transporting the entire geometric coaction through scheme isomorphisms. -/
theorem comparison_isIso_of_transport (D : BeckDescent.SheafDatum f)
    (h : IsIso (BeckDescent.invariantComparison g
      ((transportDatum f g i j w).obj D)).f) :
    IsIso (BeckDescent.invariantComparison f D).f := by
  have := pullback_isEquivalence i
  have := pullback_isEquivalence j
  have : IsIso (DescentRestriction.rightMate
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g) (pullbackSquareIso f g i j w)) := by
    rw [rightMate_eq]
    exact baseChangeMap_isIso f g i j w
  have hmap : IsIso ((Scheme.Modules.pullback i.hom).map
      (BeckDescent.invariantComparison f D).f) :=
    @InvariantComparison.comparison_map_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g) (pullbackSquareIso f g i j w)
      inferInstance inferInstance inferInstance inferInstance D h
  exact isIso_of_reflects_iso (BeckDescent.invariantComparison f D).f
    (Scheme.Modules.pullback i.hom)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IsoDescent
