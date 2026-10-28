import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL

noncomputable section

/-! Genuine PEL family isomorphisms and their base-change coherence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {g N : ℕ} {δ : Fin g → ℕ} {S T V : Scheme}

structure Iso.PolarizedActionIso (A B : Has.PolarizedActionData E g δ N S) where
  polarized : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.polarized B.polarized
  action : ∀ a : NumberField.RingOfIntegers E,
    A.action.map a ≫ polarized.abelian.hom = polarized.abelian.hom ≫ B.action.map a

namespace Iso.PolarizedActionIso

variable {A B C : Has.PolarizedActionData E g δ N S}

def refl (A : Has.PolarizedActionData E g δ N S) : PolarizedActionIso A A where
  polarized := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl A.polarized
  action a := by simp [AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl]

def symm (e : PolarizedActionIso A B) : PolarizedActionIso B A where
  polarized := e.polarized.symm
  action a := by
    change B.action.map a ≫ e.polarized.abelian.inv =
      e.polarized.abelian.inv ≫ A.action.map a
    apply (cancel_epi e.polarized.abelian.hom).mp
    rw [← Category.assoc, ← e.action a]
    simp

def trans (e : PolarizedActionIso A B) (f : PolarizedActionIso B C) :
    PolarizedActionIso A C where
  polarized := e.polarized.trans f.polarized
  action a := by
    change A.action.map a ≫ (e.polarized.abelian.hom ≫ f.polarized.abelian.hom) =
      (e.polarized.abelian.hom ≫ f.polarized.abelian.hom) ≫ C.action.map a
    rw [← Category.assoc, e.action a, Category.assoc, f.action a, Category.assoc]

def pullback (e : PolarizedActionIso A B) (f : T ⟶ S) :
    PolarizedActionIso (A.pullback f) (B.pullback f) where
  polarized := e.polarized.pullback f
  action a := ((Over.pullback f).map_comp _ _).symm.trans
    ((congrArg (fun m ↦ (Over.pullback f).map m) (e.action a)).trans
      ((Over.pullback f).map_comp _ _))

def pullbackId (A : Has.PolarizedActionData E g δ N S) :
    PolarizedActionIso (A.pullback (𝟙 S)) A where
  polarized := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.polarized
  action a := by
    change (Over.pullback (𝟙 S)).map (A.action.map a) ≫
        A.polarized.abelian.pullbackIdIso.hom =
      A.polarized.abelian.pullbackIdIso.hom ≫ A.action.map a
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality (A.action.map a)

def pullbackComp (A : Has.PolarizedActionData E g δ N S) (f : T ⟶ S) (h : V ⟶ T) :
    PolarizedActionIso ((A.pullback f).pullback h) (A.pullback (h ≫ f)) where
  polarized := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A.polarized f h
  action a := by
    change (Over.pullback h).map ((Over.pullback f).map (A.action.map a)) ≫
        (A.polarized.abelian.pullbackCompIso f h).inv =
      (A.polarized.abelian.pullbackCompIso f h).inv ≫
        (Over.pullback (h ≫ f)).map (A.action.map a)
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
    exact (Over.pullbackComp h f).inv.naturality (A.action.map a)

end Iso.PolarizedActionIso

section

variable {A : Has.PolarizedActionData E g δ N S} {B : Has.PolarizedActionData E g δ N T}
  {f : V ⟶ S} {h : V ⟶ T}

def Has.PulledBackPELDataIso.toActionIso (e : Has.PulledBackPELDataIso A B f h) :
    Iso.PolarizedActionIso (A.pullback f) (B.pullback h) where
  polarized := {
    abelian := e.abelian
    dual := e.dual
    abelianGroup := e.abelianGroup
    dualGroup := e.dualGroup
    polarization := e.polarization
    poincare :=
      (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dual.hom ⊗ₘ e.abelian.hom).left)
        (BaseChange.poincareClass_pullback B h)).trans
        ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e.dual.hom ⊗ₘ e.abelian.hom).left
          (AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap B.polarized.dual h)
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.polarized.dual.poincare)).symm.trans
          (e.poincare.trans (BaseChange.poincareClass_pullback A f).symm))
    level := e.level }
  action := e.action

def Has.PulledBackPELDataIso.ofActionIso (e : Iso.PolarizedActionIso (A.pullback f) (B.pullback h)) :
    Has.PulledBackPELDataIso A B f h where
  abelian := e.polarized.abelian
  dual := e.polarized.dual
  abelianGroup := e.polarized.abelianGroup
  dualGroup := e.polarized.dualGroup
  polarization := e.polarized.polarization
  poincare := by
    rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    rw [← BaseChange.poincareClass_pullback B h, ← BaseChange.poincareClass_pullback A f]
    exact e.polarized.poincare
  level := e.polarized.level
  action := e.action

end

variable {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {K : Type} [Field K] [NumberField K] {iota : E →+* K}
  {X Y : Over (Spec (.of K))}

/-- The two presentations use exactly the same isomorphism equations. -/
def Iso.actionIsoOfPELPullback {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N X}
    {A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N Y} {f : Y ⟶ X}
    (e : AbelianModuli.ReferenceFamily.Models.PELPullbackIso U A f) :
    Iso.PolarizedActionIso (Has.characteristicZeroPELData P A)
      ((Has.characteristicZeroPELData P U).pullback f.left) where
  polarized := {
    abelian := e.abelian
    dual := e.dual
    abelianGroup := e.abelianGroup
    dualGroup := e.dualGroup
    polarization := e.polarization
    poincare :=
      (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dual.hom ⊗ₘ e.abelian.hom).left)
        (BaseChange.poincareClass_pullback (Has.characteristicZeroPELData P U) f.left)).trans
        ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e.dual.hom ⊗ₘ e.abelian.hom).left
          (AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap U.polarized.dual f.left)
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf U.polarized.dual.poincare)).symm.trans e.poincare)
    level := e.level }
  action := e.action

def Iso.pelPullbackOfActionIso {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N X}
    {A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N Y} {f : Y ⟶ X}
    (e : Iso.PolarizedActionIso (Has.characteristicZeroPELData P A)
      ((Has.characteristicZeroPELData P U).pullback f.left)) :
    AbelianModuli.ReferenceFamily.Models.PELPullbackIso U A f where
  abelian := e.polarized.abelian
  dual := e.polarized.dual
  abelianGroup := e.polarized.abelianGroup
  dualGroup := e.polarized.dualGroup
  polarization := e.polarized.polarization
  poincare :=
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e.polarized.dual.hom ⊗ₘ e.polarized.abelian.hom).left
      (AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap U.polarized.dual f.left)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf U.polarized.dual.poincare)).trans
      ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (e.polarized.dual.hom ⊗ₘ e.polarized.abelian.hom).left)
        (BaseChange.poincareClass_pullback (Has.characteristicZeroPELData P U) f.left).symm).trans
        e.polarized.poincare)
  level := e.polarized.level
  action := e.action

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL
