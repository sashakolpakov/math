import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeFormCoherence
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamOneCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechBicomplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness

/-! # Three Cech Finiteness -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechFiniteness.IntegralFirstThreeCechFiniteness

noncomputable section

/-! Properness bounds the actual native three-term Čech cohomology through degree two. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (R : Type) [CommRing R] [IsNoetherianRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.bicomplex R X U K

def ordinaryRowIso (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech.ProperCoherentCechFiniteness.complex R X (Integral.FormsModules.IntegralFormsModules.sheaf R X n) U ≅
      (Cech.CechSheaf.functor R X U).obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n) :=
  (Cech.CechSheaf.functor R X U).mapIso (Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X n)

omit [Finite ι] in
include hU hcover in
theorem ordinary_row_finite (n : ℕ) (hn : n ≤ 2) (p : ℕ) :
    Module.Finite R (((Cech.CechSheaf.functor R X U).obj
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n)).homology p) := by
  let M := Integral.FormsModules.IntegralFormsModules.sheaf R X n
  let : M.IsQuasicoherent := ThreeFormCoherence.IntegralFirstThreeFormCoherence.quasicoherent R X n hn
  let : M.IsFiniteType := ThreeFormCoherence.IntegralFirstThreeFormCoherence.finiteType R X n hn
  let : Module.Finite R ((AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech.ProperCoherentCechFiniteness.complex R X M U).homology p) :=
    AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech.ProperCoherentCechFiniteness.finite R X M U (IsOpenCover.mk hcover) hU p
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (ordinaryRowIso R X U n) p).toLinearEquiv

omit [Finite ι] in
include hU hcover in
theorem row_finite (n : ℕ) (hn : n ≤ 2) (p : ℕ) :
    Module.Finite R (((B).X n).homology p) := by
  rcases n with _ | (_ | (_ | n))
  · exact ordinary_row_finite R X U hU hcover 0 (by omega) p
  · exact ordinary_row_finite R X U hU hcover 1 (by omega) p
  · exact ordinary_row_finite R X U hU hcover 2 (by omega) p
  · omega

omit [Finite ι] in
include hU hcover in
theorem total_finite (n : ℕ) (hn : n ≤ 2) :
    Module.Finite R (((B).total (.up ℕ)).homology n) :=
  IntegralComparison.Module.TotalFiniteness.finite B n (fun q p h => row_finite R X U hU hcover q (by omega) p)

omit [Finite ι] in
include hU hcover in
theorem sections_finite (n : ℕ) (hn : n ≤ 2) :
    Module.Finite R ((IntrinsicCech.Terms.IntrinsicCechComparison.sections R X.left U K).homology (n : ℤ)) := by
  let : Module.Finite R (((B).total (.up ℕ)).homology n) := total_finite R X U hU hcover n hn
  let : Module.Finite R ((IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.integerTotal R X U K).homology (n : ℤ)) :=
    Module.Finite.equiv (((B).total (.up ℕ)).extendHomologyIso ComplexShape.embeddingUpNat
      (j := n) rfl).symm.toLinearEquiv
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso (IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.iso R X U K) (n : ℤ)).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechFiniteness.IntegralFirstThreeCechFiniteness
