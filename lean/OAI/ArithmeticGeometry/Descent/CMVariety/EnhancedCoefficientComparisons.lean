import OAI.ArithmeticGeometry.Descent.CMVariety.ModuliObjects
import OAI.ArithmeticGeometry.Descent.CMVariety.RestrictedTupleComparison

/-! # Enhanced Coefficient Comparisons -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
The coefficient and restriction comparisons preserve the complete
enhanced abelian data: polarization, Poincare class, full level, and
every original endomorphism. Their underlying abelian isomorphisms are
exactly those used in the checked tuple-spreading theorems.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N r : ℕ} {δ : Fin g → ℕ} {S T U : Scheme}

def ModuliObjects.Abelian.EnhancedAbelianIso.pullbackCongr (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (f h : T ⟶ S) (w : f = h) : ModuliObjects.Abelian.EnhancedAbelianIso (A.pullback f) (A.pullback h) := by
  cases w
  exact ModuliObjects.Abelian.EnhancedAbelianIso.refl _

theorem ModuliObjects.Abelian.EnhancedAbelianIso.pullbackCongr_abelian (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (f h : T ⟶ S) (w : f = h) :
    (ModuliObjects.Abelian.EnhancedAbelianIso.pullbackCongr A f h w).polarized.abelian =
      A.polarized.abelian.pullbackCongrIso f h w := by
  cases w
  rfl

theorem ModuliObjects.Abelian.EnhancedAbelianIso.trans_abelian
    {A B C : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S} (e : ModuliObjects.Abelian.EnhancedAbelianIso A B) (d : ModuliObjects.Abelian.EnhancedAbelianIso B C) :
    (e.trans d).polarized.abelian = e.polarized.abelian ≪≫ d.polarized.abelian := rfl

theorem ModuliObjects.Abelian.EnhancedAbelianIso.trans_abelian_of_eq
    {A B C : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S} (e : ModuliObjects.Abelian.EnhancedAbelianIso A B) (d : ModuliObjects.Abelian.EnhancedAbelianIso B C)
    (ea : A.polarized.abelian.scheme ≅ B.polarized.abelian.scheme)
    (da : B.polarized.abelian.scheme ≅ C.polarized.abelian.scheme)
    (he : e.polarized.abelian = ea) (hd : d.polarized.abelian = da) :
    (e.trans d).polarized.abelian = ea ≪≫ da := by
  rw [ModuliObjects.Abelian.EnhancedAbelianIso.trans_abelian, he, hd]

def EnhancedCoefficientComparisons.Abelian.iteratedEnhancedPullbackIso (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p) :
    ModuliObjects.Abelian.EnhancedAbelianIso ((A.pullback f).pullback h) (A.pullback p) :=
  (ModuliObjects.Abelian.EnhancedAbelianIso.pullbackComp A f h).trans
    (ModuliObjects.Abelian.EnhancedAbelianIso.pullbackCongr A (h ≫ f) p hp)

theorem EnhancedCoefficientComparisons.Abelian.iteratedEnhancedPullbackIso_abelian (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p) :
    (EnhancedCoefficientComparisons.Abelian.iteratedEnhancedPullbackIso A f h p hp).polarized.abelian =
      AbelianCoefficientComparison.iteratedAbelianPullbackIso A.polarized.abelian f h p hp := by
  cases hp
  rfl

def EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison
    (G : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p)
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r U) (e : ModuliObjects.Abelian.EnhancedAbelianIso (G.pullback p) A) :
    ModuliObjects.Abelian.EnhancedAbelianIso ((G.pullback f).pullback h) A :=
  (EnhancedCoefficientComparisons.Abelian.iteratedEnhancedPullbackIso G f h p hp).trans e

theorem EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison_abelian
    (G : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p)
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r U) (e : ModuliObjects.Abelian.EnhancedAbelianIso (G.pullback p) A) :
    (EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison G f h p hp A e).polarized.abelian =
      RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison G.polarized.abelian f h p hp A.polarized.abelian
        e.polarized.abelian := by
  dsimp only [EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison, RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison]
  rw [ModuliObjects.Abelian.EnhancedAbelianIso.trans_abelian, EnhancedCoefficientComparisons.Abelian.iteratedEnhancedPullbackIso_abelian]
  rfl

theorem EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison_abelian_of_eq
    (G : ModuliObjects.Abelian.EnhancedAbelianData g δ N r S)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p)
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r U) (e : ModuliObjects.Abelian.EnhancedAbelianIso (G.pullback p) A)
    (ea : (G.polarized.abelian.pullback p).scheme ≅ A.polarized.abelian.scheme)
    (he : e.polarized.abelian = ea) :
    (EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison G f h p hp A e).polarized.abelian =
      RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison G.polarized.abelian f h p hp A.polarized.abelian ea :=
  (EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison_abelian G f h p hp A e).trans
    (congrArg (RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison G.polarized.abelian f h p hp A.polarized.abelian) he)

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ) :
    ModuliObjects.Abelian.EnhancedAbelianIso
      ((A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).pullback (AbelianCoefficientComparison.coefficientInclusion R B s))
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :=
  EnhancedCoefficientComparisons.Abelian.iteratedEnhancedPullbackIso A (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)
    (AbelianCoefficientComparison.coefficientInclusion R B s) _ (AbelianCoefficientComparison.coefficientInclusion_base R B s)

theorem EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison_abelian
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ) :
    (EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison R B A s).polarized.abelian =
      AbelianCoefficientComparison.abelianCoefficientComparison R B A.polarized.abelian s :=
  EnhancedCoefficientComparisons.Abelian.iteratedEnhancedPullbackIso_abelian A _ _ _ (AbelianCoefficientComparison.coefficientInclusion_base R B s)

def EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of R))) (s t : (Finset B)ᵒᵖ) :
    ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of
      (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t.unop))) :=
  (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).pullback
    (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t.unop)

def EnhancedCoefficientComparisons.Abelian.twoStageEnhancedComparison
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of R))) (s t : (Finset B)ᵒᵖ) :
    ModuliObjects.Abelian.EnhancedAbelianIso
      ((EnhancedCoefficientComparisons.Abelian.twoStageEnhancedFamily R B A s t).pullback
        (AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t))
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :=
  (EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B
    (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) t).trans
      (EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison R B A s)

theorem EnhancedCoefficientComparisons.Abelian.twoStageEnhancedComparison_abelian
    (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r (Spec (CommRingCat.of R))) (s t : (Finset B)ᵒᵖ) :
    (EnhancedCoefficientComparisons.Abelian.twoStageEnhancedComparison R B A s t).polarized.abelian =
      AbelianEndomorphism.twoStageCoefficientComparison R B A.polarized.abelian s t := by
  exact ModuliObjects.Abelian.EnhancedAbelianIso.trans_abelian_of_eq
    (EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B
      (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) t)
    (EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison R B A s)
    (AbelianCoefficientComparison.abelianCoefficientComparison (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B
      (A.polarized.abelian.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) t)
    (AbelianCoefficientComparison.abelianCoefficientComparison R B A.polarized.abelian s)
    (EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison_abelian _ _ _ _) (EnhancedCoefficientComparisons.Abelian.coefficientEnhancedComparison_abelian _ _ _ _)

end

end OAI.ArithmeticGeometry.Descent.CMVariety
