import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal
import Mathlib.Algebra.Homology.Embedding.Extend

/-! # Resolution Integer -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionInteger.FunctorResolutionInteger

noncomputable section

/-! The natural total-resolution square remains the actual square after extension to integer degrees. -/

open _root_.CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  (G : C ⥤ CochainComplex C ℕ) [G.Additive]
  (η : CochainComplex.single₀ C ⟶ G)

def total (K : CochainComplex C ℕ) : CochainComplex C ℤ :=
  (ResolutionTotal.FunctorResolutionTotal.total G K).extend ComplexShape.embeddingUpNat

def map {K L : CochainComplex C ℕ} (f : K ⟶ L) : total G K ⟶ total G L :=
  HomologicalComplex.extendMap (ResolutionTotal.FunctorResolutionTotal.map G f) ComplexShape.embeddingUpNat

def edge (K : CochainComplex C ℕ) : K.extend ComplexShape.embeddingUpNat ⟶ total G K :=
  HomologicalComplex.extendMap (ResolutionTotal.FunctorResolutionTotal.edge G η K) ComplexShape.embeddingUpNat

theorem naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    edge G η K ≫ map G f = HomologicalComplex.extendMap f ComplexShape.embeddingUpNat ≫ edge G η L :=
  (HomologicalComplex.extendMap_comp (ResolutionTotal.FunctorResolutionTotal.edge G η K)
    (ResolutionTotal.FunctorResolutionTotal.map G f) ComplexShape.embeddingUpNat).symm.trans
      ((congrArg (fun a => HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)
        (ResolutionTotal.FunctorResolutionTotal.naturality G η f)).trans
          (HomologicalComplex.extendMap_comp f (ResolutionTotal.FunctorResolutionTotal.edge G η L)
            ComplexShape.embeddingUpNat))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionInteger.FunctorResolutionInteger
