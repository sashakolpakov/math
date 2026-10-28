import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness

/-! # Cech Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechFiniteness.Intrinsic

noncomputable section

/-! Finite cohomology of the original sheafified de Rham complex on
any actual affine cover of a smooth proper scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom] {ι : Type u} (U : ι → X.left.Opens)

def rowIso (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech.ProperCoherentCechFiniteness.complex R X
      (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.term R X n) U ≅
        (CechComplex.Intrinsic.bicomplex R X U).X n :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).mapIso
    ((CechComplex.Intrinsic.presheaves R X).mapIso (AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormSheaf.OrdinaryFormSheafComparison.iso R X n))

variable [IsNoetherianRing R] (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
include hU hUaff

theorem row_finite (n q : ℕ) :
    Module.Finite R (((CechComplex.Intrinsic.bicomplex R X U).X n).homology q) := by
  let M := AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.term R X n
  let : M.IsQuasicoherent := AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.quasicoherent R X n
  let : M.IsFiniteType := AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.finiteType R X n
  let : Module.Finite R ((AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech.ProperCoherentCechFiniteness.complex R X M U).homology q) :=
    AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech.ProperCoherentCechFiniteness.finite R X M U hU hUaff q
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (rowIso R X U n) q).toLinearEquiv

theorem finite (n : ℕ) : Module.Finite R ((CechComplex.Intrinsic.total R X U).homology n) :=
  IntegralComparison.Module.TotalFiniteness.finite (CechComplex.Intrinsic.bicomplex R X U) n
    (fun q p _ => row_finite R X U hU hUaff q p)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechFiniteness.Intrinsic
