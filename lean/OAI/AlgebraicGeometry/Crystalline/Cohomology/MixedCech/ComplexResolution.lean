import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ResolutionSheafQuasiIso
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ZariskiColimitsCore
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.CochainComplexPlus

/-! # Complex Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.ComplexResolution.MixedCechComplexResolution

noncomputable section

/-! # The actual Čech total resolves complexes of coefficient sheaves in every universe -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens)

abbrev Sheaves := Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)

local instance : HasCoproducts.{0} (Sheaves R X) := ZariskiColimitsCore.ZariskiColimits.coproducts R X

variable (K : CochainComplex (Sheaves R X) ℕ)

def total : CochainComplex (Sheaves R X) ℕ :=
  NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal.FunctorResolutionTotal.total (Functor.MixedCechFunctor.sheafFunctor R X U) K

def edge : K ⟶ total R X U K :=
  NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal.FunctorResolutionTotal.edge (Functor.MixedCechFunctor.sheafFunctor R X U)
    (Functor.MixedCechFunctor.sheafAugmentation R X U) K

theorem edge_quasiIso (hU : iSup U = ⊤) : QuasiIso (edge R X U K) :=
  @ResolutionSheafQuasiIso.FunctorResolutionSheafQuasiIso.quasiIso R _ (TopCat.of X)
    (Functor.MixedCechFunctor.sheafFunctor R X U) (Functor.MixedCechFunctor.sheaf_additive R X U)
    (Functor.MixedCechFunctor.sheafAugmentation R X U)
    (Functor.MixedCechFunctor.sheafAugmentation_quasiIso R X U hU) K

def integerTotal : CochainComplex (Sheaves R X) ℤ :=
  (total R X U K).extend ComplexShape.embeddingUpNat

instance integerTotal_nonnegative : (integerTotal R X U K).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((total R X U K).extend ComplexShape.embeddingUpNat) 0)

def integerEdge : K.extend ComplexShape.embeddingUpNat ⟶ integerTotal R X U K :=
  HomologicalComplex.extendMap (edge R X U K) ComplexShape.embeddingUpNat

theorem integerEdge_quasiIso (hU : iSup U = ⊤) : QuasiIso (integerEdge R X U K) :=
  (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr (edge_quasiIso R X U K hU)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.ComplexResolution.MixedCechComplexResolution
