import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelKoszulDualComparison

/-! # Model Tensor Koszul Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelTensorKoszulComparison

noncomputable section

/-! The comparison with the explicit Koszul dual survives every additive functor, including tensoring by any module. This follows from homotopies of the actual dual projective resolutions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u v w x

def dualHomotopyEquivMappedHomologyIso
    {R : Type u} [CommRing R] {ι : Type x} {c : ComplexShape ι}
    {V : Type v} [Category.{w} V] [Abelian V]
    (F : ModuleCat.{u} R ⥤ V) [F.Additive]
    {K L : HomologicalComplex (ModuleCat.{u} R) c.symm}
    (e : HomotopyEquiv K L) (i : ι) :
    ((F.mapHomologicalComplex c).obj (HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm K)).homology i ≅
      ((F.mapHomologicalComplex c).obj (HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm L)).homology i :=
  ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMapHomologyIso F
    (Dual.ShortComplexHomotopy.dualShortComplexHomotopyEquiv (Dual.ResolutionHomologyComparison.homotopyEquivShortComplex e i))

def minimalModelMappedKoszulDualHomologyIso
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {V : Type v} [Category.{w} V] [Abelian V]
    (F : ModuleCat.{u} R ⥤ V) [F.Additive]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (hbound : ∀ q, g < q → IsZero (C.X q))
    (rs : List R) (hlen : rs.length = g) (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R) (hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R))
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))
    (e : R ≃ₗ[R] Q.complex.X₁) (hI : Q.firstDifferentialIdeal = maximalIdeal R) (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℕ)).obj C).homology n ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj
        (HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) (Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs))).homology n :=
  HomologicalComplex.homologyMapIso
    ((F.mapHomologicalComplex (.up ℕ)).mapIso (HilbertConstruction.Finite.FreeDoubleDualComplex.finiteFreeDoubleDualComplexIso C hfin hfree)) n ≪≫
    dualHomotopyEquivMappedHomologyIso F
      ((AugmentedDualProjectiveResolution.minimalDualProjectiveResolution C g hfin hfree hbound rs hlen hreg hgen hfield Q e hI).homotopyEquiv
        (Regular.ParameterKoszulResolution.regularParameterKoszulResolution rs hreg hgen)) n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelTensorKoszulComparison
