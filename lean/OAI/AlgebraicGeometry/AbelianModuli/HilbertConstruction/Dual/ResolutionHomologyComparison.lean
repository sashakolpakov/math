import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeDoubleDualComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ShortComplexHomotopy
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ResolutionComparison

/-! # Resolution Homology Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ResolutionHomologyComparison

noncomputable section

/-! Homotopy equivalent chain resolutions have isomorphic cohomology after taking module duals. The proof compares their actual short complexes in each degree, so it also handles the endpoint. -/
open _root_.CategoryTheory
universe u v w

def homotopyEquivShortComplex
    {V : Type u} [Category.{v} V] [Preadditive V] {ι : Type w} {c : ComplexShape ι}
    {K L : HomologicalComplex V c} (e : HomotopyEquiv K L) (i : ι) :
    ShortComplex.HomotopyEquiv (K.sc i) (L.sc i) where
  hom := (HomologicalComplex.shortComplexFunctor V c i).map e.hom
  inv := (HomologicalComplex.shortComplexFunctor V c i).map e.inv
  homotopyHomInvId := by
    classical
    have h := e.homotopyHomInvId.toShortComplex i
    rw [(HomologicalComplex.shortComplexFunctor V c i).map_comp e.hom e.inv,
      (HomologicalComplex.shortComplexFunctor V c i).map_id K] at h
    exact h
  homotopyInvHomId := by
    classical
    have h := e.homotopyInvHomId.toShortComplex i
    rw [(HomologicalComplex.shortComplexFunctor V c i).map_comp e.inv e.hom,
      (HomologicalComplex.shortComplexFunctor V c i).map_id L] at h
    exact h

def dualHomotopyEquivHomologyIso
    {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c.symm}
    (e : HomotopyEquiv K L) (i : ι) :
    (Finite.FreeDoubleDualComplex.dualModuleComplexSymm K).homology i ≅ (Finite.FreeDoubleDualComplex.dualModuleComplexSymm L).homology i :=
  ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivHomologyIso
    (ShortComplexHomotopy.dualShortComplexHomotopyEquiv (homotopyEquivShortComplex e i))

def dualProjectiveResolutionHomologyIso
    {R : Type u} [CommRing R] {Z : ModuleCat.{u} R}
    (P Q : Projective.ResolutionBasic.ProjectiveResolution Z) (n : ℕ) :
    (Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) P.complex).homology n ≅
      (Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) Q.complex).homology n :=
  dualHomotopyEquivHomologyIso (P.homotopyEquiv Q) n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ResolutionHomologyComparison
