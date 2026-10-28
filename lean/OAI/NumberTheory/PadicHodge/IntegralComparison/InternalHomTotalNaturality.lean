import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology

/-! # Internal Hom Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalNaturality

noncomputable section

/-! Naturality of the actual Hom-to-Čech-total comparison. This applies
to the maps of resolutions supplied by a common negative refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (N : X.Modules)
  {K L : CochainComplex X.Modulesᵒᵖ ℕ} (a : K ⟶ L)

def homMap : InternalHomCechTotal.homComplex N K ⟶ InternalHomCechTotal.homComplex N L :=
  ((preadditiveYoneda.obj N).mapHomologicalComplex (.up ℕ)).map a

def internalMap : InternalHomCechTotal.internalComplex N K ⟶ InternalHomCechTotal.internalComplex N L :=
  ((SchemeInternalHom.functor N).mapHomologicalComplex (.up ℕ)).map a

def sectionMap :=
  ((forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
    (OrderedCech.TotalNaturality.sectionMap π (internalMap N a))

def totalMap : InternalHomCechTotal.additiveTotal π U N K ⟶ InternalHomCechTotal.additiveTotal π U N L :=
  ((forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
    (OrderedCech.QuasiIso.map π U (internalMap N a))

@[reassoc]
theorem sections_naturality : homMap N a ≫ (InternalHomCechTotal.sectionComplexIso π N L).hom =
    (InternalHomCechTotal.sectionComplexIso π N K).hom ≫ sectionMap π N a :=
  ((SchemeInternalHom.globalSectionsIso N).hom.mapHomologicalComplex (.up ℕ)).naturality a

def edge (K : CochainComplex X.Modulesᵒᵖ ℕ) (hU : iSup U = ⊤) :=
  ((forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
    (OrderedCech.Total.Comparison.edge π U (InternalHomCechTotal.internalComplex N K) hU)

@[reassoc]
theorem edge_naturality (hU : iSup U = ⊤) :
    sectionMap π N a ≫ edge π U N L hU = edge π U N K hU ≫ totalMap π U N a := by
  let F := (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).mapHomologicalComplex (.up ℕ)
  exact (DualComplexHomology.map_square F _ _ _ _
    (OrderedCech.TotalNaturality.edge_naturality π U (internalMap N a) hU)).symm

def comparisonMap (K : CochainComplex X.Modulesᵒᵖ ℕ) (hU : iSup U = ⊤) :
    InternalHomCechTotal.homComplex N K ⟶ InternalHomCechTotal.additiveTotal π U N K :=
  (InternalHomCechTotal.sectionComplexIso π N K).hom ≫ edge π U N K hU

@[reassoc]
theorem comparisonMap_naturality (hU : iSup U = ⊤) :
    homMap N a ≫ comparisonMap π U N L hU =
      comparisonMap π U N K hU ≫ totalMap π U N a := by
  rw [comparisonMap, comparisonMap, ← Category.assoc, sections_naturality,
    Category.assoc, edge_naturality, ← Category.assoc]

@[reassoc]
theorem homology_naturality (hU : iSup U = ⊤)
    (hK : InternalHomCechTotal.TermsAcyclic π U N K) (hL : InternalHomCechTotal.TermsAcyclic π U N L) (n : ℕ) :
    HomologicalComplex.homologyMap (homMap N a) n ≫ (InternalHomCechTotal.homologyIso π U N L hU hL n).hom =
      (InternalHomCechTotal.homologyIso π U N K hU hK n).hom ≫ HomologicalComplex.homologyMap (totalMap π U N a) n := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (comparisonMap_naturality π U N a hU)
  simpa only [comparisonMap, edge, InternalHomCechTotal.homologyIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom,
    isoOfQuasiIsoAt_hom, HomologicalComplex.homologyMap_comp, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalNaturality
