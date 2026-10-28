import OAI.ArithmeticGeometry.Descent.CMVariety.AffineCoefficientObjects

/-! # Coefficient Object Base Change -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! Enlarge an object's finite coefficient ring while retaining its exact
complex fiber and all finite-presentation properties. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def CoefficientObjectBaseChange.Abelian.objectCoefficientMap {s t : Finset B} (h : s ⊆ t) :
    Spec (CommRingCat.of (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B t)) ⟶
      Spec (CommRingCat.of (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s)) :=
  Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h))).toRingHom)

def CoefficientObjectBaseChange.Abelian.objectCoefficientPoint (s : Finset B) : Spec (CommRingCat.of B) ⟶
    Spec (CommRingCat.of (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s) B))

theorem CoefficientObjectBaseChange.Abelian.objectCoefficientPoint_map {s t : Finset B} (h : s ⊆ t) :
    CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B t ≫ CoefficientObjectBaseChange.Abelian.objectCoefficientMap R B h = CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B s := by
  dsimp only [CoefficientObjectBaseChange.Abelian.objectCoefficientPoint, CoefficientObjectBaseChange.Abelian.objectCoefficientMap]
  rw [← Spec.map_comp]
  congr 1

def CoefficientObjectBaseChange.Abelian.overPullbackPointCongr {S T : Scheme} {f g : T ⟶ S} (h : f = g) (M : Over S) :
    (Over.pullback f).obj M ≅ (Over.pullback g).obj M := by
  subst g
  exact Iso.refl _

def CoefficientObjectBaseChange.Abelian.iteratedObjectPullbackIso {S T V : Scheme}
    (f : T ⟶ S) (q : V ⟶ T) (p : V ⟶ S) (h : q ≫ f = p) (M : Over S) :
    (Over.pullback q).obj ((Over.pullback f).obj M) ≅ (Over.pullback p).obj M :=
  (Over.pullbackComp q f).symm.app M ≪≫ CoefficientObjectBaseChange.Abelian.overPullbackPointCongr h M

variable {R B}

def AffineCoefficientObjects.Abelian.CoefficientSchemeModel.specialization {X : Over (Spec (CommRingCat.of B))}
    (M : AffineCoefficientObjects.Abelian.CoefficientSchemeModel R B X) : X.left ⟶ M.model.left :=
  M.comparison.inv.left ≫ pullback.fst M.model.hom (CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B M.coefficients)

theorem AffineCoefficientObjects.Abelian.CoefficientSchemeModel.cartesian {X : Over (Spec (CommRingCat.of B))}
    (M : AffineCoefficientObjects.Abelian.CoefficientSchemeModel R B X) :
    IsPullback M.specialization X.hom M.model.hom (CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B M.coefficients) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    ((Over.forget (Spec (CommRingCat.of B))).mapIso M.comparison.symm) rfl ?_
  · dsimp only [AffineCoefficientObjects.Abelian.CoefficientSchemeModel.specialization]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => M.comparison.inv.left ≫ f)
        (pullback.condition (f := M.model.hom) (g := CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B M.coefficients))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B M.coefficients) M.comparison.inv.w)))
  · exact M.comparison.inv.w

def AffineCoefficientObjects.Abelian.CoefficientSchemeModel.ofCartesian {X : Over (Spec (CommRingCat.of B))}
    (s : Finset B) (Y : Over (Spec (CommRingCat.of (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s))))
    (hFP : LocallyOfFinitePresentation Y.hom) (hQC : QuasiCompact Y.hom) (hQS : QuasiSeparated Y.hom)
    (f : X.left ⟶ Y.left) (h : IsPullback f X.hom Y.hom (CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B s)) :
    AffineCoefficientObjects.Abelian.CoefficientSchemeModel R B X where
  coefficients := s
  model := Y
  finitePresentation := hFP
  quasiCompact := hQC
  quasiSeparated := hQS
  comparison := Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd

theorem AffineCoefficientObjects.Abelian.CoefficientSchemeModel.ofCartesian_specialization {X : Over (Spec (CommRingCat.of B))}
    (s : Finset B) (Y : Over (Spec (CommRingCat.of (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s))))
    (hFP : LocallyOfFinitePresentation Y.hom) (hQC : QuasiCompact Y.hom) (hQS : QuasiSeparated Y.hom)
    (f : X.left ⟶ Y.left) (h : IsPullback f X.hom Y.hom (CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B s)) :
    (AffineCoefficientObjects.Abelian.CoefficientSchemeModel.ofCartesian s Y hFP hQC hQS f h).specialization = f := h.isoPullback_hom_fst

def AffineCoefficientObjects.Abelian.CoefficientSchemeModel.enlarge {X : Over (Spec (CommRingCat.of B))}
    (M : AffineCoefficientObjects.Abelian.CoefficientSchemeModel R B X) (t : Finset B) (h : M.coefficients ⊆ t) :
    AffineCoefficientObjects.Abelian.CoefficientSchemeModel R B X where
  coefficients := t
  model := (Over.pullback (CoefficientObjectBaseChange.Abelian.objectCoefficientMap R B h)).obj M.model
  finitePresentation := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.snd M.model.hom (CoefficientObjectBaseChange.Abelian.objectCoefficientMap R B h)))
  quasiCompact := inferInstanceAs
    (QuasiCompact (pullback.snd M.model.hom (CoefficientObjectBaseChange.Abelian.objectCoefficientMap R B h)))
  quasiSeparated := inferInstanceAs
    (QuasiSeparated (pullback.snd M.model.hom (CoefficientObjectBaseChange.Abelian.objectCoefficientMap R B h)))
  comparison := CoefficientObjectBaseChange.Abelian.iteratedObjectPullbackIso (CoefficientObjectBaseChange.Abelian.objectCoefficientMap R B h)
    (CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B t) (CoefficientObjectBaseChange.Abelian.objectCoefficientPoint R B M.coefficients)
    (CoefficientObjectBaseChange.Abelian.objectCoefficientPoint_map R B h) M.model ≪≫ M.comparison

end

end OAI.ArithmeticGeometry.Descent.CMVariety
