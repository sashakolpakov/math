import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

/-! # Presentation Composition -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Keep the actual subgroup carrier when composing its ambient
inclusion or pulling the full presentation across a scheme base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Intrinsic.Neighbors.KernelPresentation.postcomp {S : Scheme} {A B : Over S}
    (K : Intrinsic.Neighbors.KernelPresentation A) (i : A ⟶ B) : Intrinsic.Neighbors.KernelPresentation B :=
  ⟨K.carrier, K.inclusion ≫ i⟩

def Intrinsic.Neighbors.KernelPresentation.postcompCarrierIso {S : Scheme} {A B : Over S}
    (K : Intrinsic.Neighbors.KernelPresentation A) (i : A ⟶ B) : K.carrier ≅ (K.postcomp i).carrier :=
  Iso.refl K.carrier

theorem Intrinsic.Neighbors.KernelPresentation.postcompCarrierIso_inclusion {S : Scheme} {A B : Over S}
    (K : Intrinsic.Neighbors.KernelPresentation A) (i : A ⟶ B) :
    (K.postcompCarrierIso i).hom ≫ (K.postcomp i).inclusion = K.inclusion ≫ i :=
  Category.id_comp (K.inclusion ≫ i)

theorem Intrinsic.Neighbors.KernelPresentation.postcomp_assoc {S : Scheme} {A B C : Over S}
    (K : Intrinsic.Neighbors.KernelPresentation A) (i : A ⟶ B) (j : B ⟶ C) :
    (K.postcomp i).postcomp j = K.postcomp (i ≫ j) := by
  exact congrArg (Intrinsic.Neighbors.KernelPresentation.mk K.carrier) (Category.assoc K.inclusion i j)

theorem Intrinsic.Neighbors.KernelPresentation.pullback_postcomp {S T : Scheme} {A B : Over S}
    (K : Intrinsic.Neighbors.KernelPresentation A) (i : A ⟶ B) (b : T ⟶ S) :
    (K.postcomp i).pullback b = (K.pullback b).postcomp ((Over.pullback b).map i) :=
  congrArg (Intrinsic.Neighbors.KernelPresentation.mk ((Over.pullback b).obj K.carrier))
    ((Over.pullback b).map_comp K.inclusion i)

theorem Intrinsic.Neighbors.KernelPresentation.pullback_postcomp_eq {S T : Scheme} {A B : Over S} {C : Over T}
    (K : Intrinsic.Neighbors.KernelPresentation A) (i : A ⟶ B) (b : T ⟶ S)
    (j : (Over.pullback b).obj B ⟶ C)
    (P : Intrinsic.Neighbors.KernelPresentation ((Over.pullback b).obj A)) (h : K.pullback b = P) :
    ((K.postcomp i).pullback b).postcomp j =
      P.postcomp ((Over.pullback b).map i ≫ j) :=
  (congrArg (fun Q => Q.postcomp j) (K.pullback_postcomp i b)).trans
    (((K.pullback b).postcomp_assoc ((Over.pullback b).map i) j).trans
      (congrArg (fun Q => Q.postcomp ((Over.pullback b).map i ≫ j)) h))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
