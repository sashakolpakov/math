import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Bicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionSheafQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafTotalEdge
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.CochainComplexPlus

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Resolution.IntrinsicCechResolution

noncomputable section

/-! The actual native Čech total augmentation is a quasi-isomorphism, including its integer extension. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Scheme.{0})
  {ι : Type} (U : ι → X.Opens)
  (K : CochainComplex (Bicomplex.IntrinsicCechBicomplex.Sheaves R X) ℕ)

local instance : HasCoproducts.{0} (Bicomplex.IntrinsicCechBicomplex.Sheaves R X) :=
  Instances.IntrinsicCechInstances.hasCoproducts R X

local instance : (Functor.IntrinsicCechFunctor.sheafFunctor R X U).Additive :=
  Instances.IntrinsicCechInstances.additive R X U

def total : CochainComplex (Bicomplex.IntrinsicCechBicomplex.Sheaves R X) ℕ :=
  Functor.ResolutionTotal.FunctorResolutionTotal.total (Functor.IntrinsicCechFunctor.sheafFunctor R X U) K

def integerTotal : CochainComplex (Bicomplex.IntrinsicCechBicomplex.Sheaves R X) ℤ :=
  (total R X U K).extend ComplexShape.embeddingUpNat

instance integerTotal_nonnegative : (integerTotal R X U K).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((total R X U K).extend ComplexShape.embeddingUpNat) 0)

theorem edge_quasiIso (hU : iSup U = ⊤) : QuasiIso (Bicomplex.IntrinsicCechBicomplex.edge R X U K) :=
  @Functor.ResolutionSheafQuasiIso.FunctorResolutionSheafQuasiIso.quasiIso R _ (TopCat.of X) (Functor.IntrinsicCechFunctor.sheafFunctor R X U)
    (Instances.IntrinsicCechInstances.additive R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation_quasiIso R X U hU) K

def integerEdge : K.extend ComplexShape.embeddingUpNat ⟶ integerTotal R X U K :=
  HomologicalComplex.extendMap (Bicomplex.IntrinsicCechBicomplex.edge R X U K) ComplexShape.embeddingUpNat

theorem integerEdge_quasiIso (hU : iSup U = ⊤) : QuasiIso (integerEdge R X U K) :=
  (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr (edge_quasiIso R X U K hU)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Resolution.IntrinsicCechResolution
