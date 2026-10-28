import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Resolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionInteger
import OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedHypercohomologyEquiv

/-! # Terms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Terms.IntrinsicCechComparison

noncomputable section

/-! A natural section comparison for the actual native Čech resolution. Its Ext hypotheses are supplied by the finite affine vanishing theorems. -/

open _root_.CategoryTheory Abelian Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Scheme.{0}) {ι : Type} (U : ι → X.Opens)

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Bicomplex.IntrinsicCechBicomplex.Sheaves R X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient R (TopCat.of X)

local instance : HasCoproducts.{0} V := Instances.IntrinsicCechInstances.hasCoproducts R X
local instance : HasExt.{1} V := HasExt.standard _
local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _
local instance : (Functor.IntrinsicCechFunctor.sheafFunctor R X U).Additive := Instances.IntrinsicCechInstances.additive R X U

def totalMap {K L : CochainComplex V ℕ} (f : K ⟶ L) :
    Resolution.IntrinsicCechResolution.integerTotal R X U K ⟶ Resolution.IntrinsicCechResolution.integerTotal R X U L :=
  @Functor.ResolutionInteger.FunctorResolutionInteger.map V _ _ (Instances.IntrinsicCechInstances.hasCoproducts R X)
    (Functor.IntrinsicCechFunctor.sheafFunctor R X U) (Instances.IntrinsicCechInstances.additive R X U) K L f

theorem edge_naturality {K L : CochainComplex V ℕ} (f : K ⟶ L) :
    Resolution.IntrinsicCechResolution.integerEdge R X U K ≫ totalMap R X U f =
      HomologicalComplex.extendMap f ComplexShape.embeddingUpNat ≫ Resolution.IntrinsicCechResolution.integerEdge R X U L :=
  @Functor.ResolutionInteger.FunctorResolutionInteger.naturality V _ _ (Instances.IntrinsicCechInstances.hasCoproducts R X)
    (Functor.IntrinsicCechFunctor.sheafFunctor R X U) (Instances.IntrinsicCechInstances.additive R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R X U) K L f

def AcyclicTerms (K : CochainComplex V ℕ) : Prop :=
  ∀ p q, Subsingleton (Ext.{1} A ((Resolution.IntrinsicCechResolution.integerTotal R X U K).X p) (q + 1))

def sections (K : CochainComplex V ℕ) : CochainComplex (ModuleCat.{0} R) ℤ :=
  Section.Hypercohomology.SectionHypercohomology.sectionComplex R (TopCat.of X) (Resolution.IntrinsicCechResolution.integerTotal R X U K)

def equiv (hcover : iSup U = ⊤) (K : CochainComplex V ℕ) (hK : AcyclicTerms R X U K) (n : ℤ) :
    (sections R X U K).homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor V 0).obj A ⟶
        (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦n⟧) := by
  have : QuasiIso (Resolution.IntrinsicCechResolution.integerEdge R X U K) :=
    Resolution.IntrinsicCechResolution.integerEdge_quasiIso R X U K hcover
  exact ResolvedHypercohomologyEquiv.ResolvedHypercohomology.equiv R (TopCat.of X)
    (Resolution.IntrinsicCechResolution.integerEdge R X U K) 0 hK n

theorem naturality (hcover : iSup U = ⊤) {K L : CochainComplex V ℕ}
    (hK : AcyclicTerms R X U K) (hL : AcyclicTerms R X U L) (f : K ⟶ L) (n : ℤ)
    (x : (sections R X U K).homology n) :
    equiv R X U hcover L hL n (HomologicalComplex.homologyMap
      (((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X)).mapHomologicalComplex (.up ℤ)).map
        (totalMap R X U f)) n x) =
      equiv R X U hcover K hK n x ≫
        (DerivedCategory.Q.map (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat))⟦n⟧' := by
  have : QuasiIso (Resolution.IntrinsicCechResolution.integerEdge R X U K) :=
    Resolution.IntrinsicCechResolution.integerEdge_quasiIso R X U K hcover
  have : QuasiIso (Resolution.IntrinsicCechResolution.integerEdge R X U L) :=
    Resolution.IntrinsicCechResolution.integerEdge_quasiIso R X U L hcover
  exact ResolvedHypercohomologyEquiv.ResolvedHypercohomology.naturality R (TopCat.of X)
    (Resolution.IntrinsicCechResolution.integerEdge R X U K) (Resolution.IntrinsicCechResolution.integerEdge R X U L)
    (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) (totalMap R X U f)
    (edge_naturality R X U f) 0 0 hK hL n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Terms.IntrinsicCechComparison
