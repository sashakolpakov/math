import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Total

/-! # Internal Hom Cech Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal

noncomputable section

/-! The ordinary Hom complex computes the actual Čech total of the
internal Hom complex when its terms have no higher Čech cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (N : X.Modules) (K : CochainComplex X.Modulesᵒᵖ ℕ)

abbrev homComplex := ((preadditiveYoneda.obj N).mapHomologicalComplex (.up ℕ)).obj K

abbrev internalComplex := SchemeInternalHom.complex (.up ℕ) N K

abbrev total := (OrderedCech.Total.Comparison.bicomplex π U (internalComplex N K)).total (.up ℕ)

abbrev additiveTotal :=
  ((forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj (InternalHomCechTotal.total π U N K)

def TermsAcyclic : Prop :=
  ∀ q p, IsZero ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π
    ((internalComplex N K).X q) U).homology (p + 1))

def sectionComplexIso : homComplex N K ≅
    ((forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
      (OrderedCech.Total.Comparison.sectionComplex π (internalComplex N K)) :=
  SchemeInternalHom.complexSectionsIso (.up ℕ) N K

def homologyIso (hU : iSup U = ⊤)
    (hK : TermsAcyclic π U N K)
    (n : ℕ) : (homComplex N K).homology n ≅ (additiveTotal π U N K).homology n := by
  let F := forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat
  let e := OrderedCech.Total.Comparison.edge π U (internalComplex N K) hU
  letI : QuasiIso e := OrderedCech.Total.Comparison.quasiIso π U (internalComplex N K) hU hK
  exact HomologicalComplex.homologyMapIso (sectionComplexIso π N K) n ≪≫
    isoOfQuasiIsoAt ((F.mapHomologicalComplex (.up ℕ)).map e) n

def ComparisonIso (n : ℕ) :=
  (homComplex N K).homology n ≅ (additiveTotal π U N K).homology n

def TotalIso (n : ℕ) (D : AddCommGrpCat.{u}) :=
  (additiveTotal π U N K).homology n ≅ D

def comparison (hU : iSup U = ⊤) (hK : TermsAcyclic π U N K) (n : ℕ) :
    ComparisonIso π U N K n :=
  homologyIso π U N K hU hK n

def ComparisonIso.symmTrans {n : ℕ} (e : ComparisonIso π U N K n)
    {D : AddCommGrpCat.{u}} (f : (homComplex N K).homology n ≅ D) :
    (additiveTotal π U N K).homology n ≅ D :=
  e.symm ≪≫ f

def chainHomologyIso (P : ChainComplex X.Modules ℕ) (hU : iSup U = ⊤)
    (hP : TermsAcyclic π U N P.op) (n : ℕ) :
    (((preadditiveYoneda.obj N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj
      P.op).homology n ≅ (additiveTotal π U N P.op).homology n :=
  homologyIso π U N P.op hU hP n

def chainComparisonTrans (P : ChainComplex X.Modules ℕ) (hU : iSup U = ⊤)
    (hP : TermsAcyclic π U N P.op) (n : ℕ) {D : AddCommGrpCat.{u}}
    (e : (((preadditiveYoneda.obj N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj
      P.op).homology n ≅ D) :
    TotalIso π U N P.op n D :=
  (chainHomologyIso π U N P hU hP n).symm ≪≫ e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal
