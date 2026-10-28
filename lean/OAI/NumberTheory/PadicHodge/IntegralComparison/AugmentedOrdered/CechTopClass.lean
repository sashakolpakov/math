import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLargeTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopRowEdge

/-! # Cech Top Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopClass

noncomputable section

/-! The ordinary augmented top class is the literal full-intersection
cocycle. Its total-complex image is the original top-row edge. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  (N : Cᵒᵖ ⥤ ModuleCat.{w} R) (m : ℕ) (hm : Fintype.card ι = m)

def topCycle (z : N.obj (op (CechCoordinates.topObject U m hm))) : Module.CochainClasses.cycles (Cech.complex U N) m :=
  ⟨CechCoordinates.topInclusion U N m hm z, by
    change (Cech.complex U N).d m (m+1) (CechCoordinates.topInclusion U N m hm z) = 0
    dsimp only [Cech.complex]
    rw [CochainComplex.of_d, CechCoordinates.differential_top U N m hm]
    rfl⟩

def topClass (z : N.obj (op (CechCoordinates.topObject U m hm))) : (Cech.complex U N).homology m :=
  Module.CochainClasses.classMap (Cech.complex U N) m (topCycle U N m hm z)

theorem topClass_naturality {P : Cᵒᵖ ⥤ ModuleCat.{w} R} (a : N ⟶ P)
    (z : N.obj (op (CechCoordinates.topObject U m hm))) :
    homologyMap (CechFunctor.complexMap U a) m (topClass U N m hm z) =
      topClass U P m hm (a.app (op (CechCoordinates.topObject U m hm)) z) := by
  simp only [topClass]
  rw [← Module.CochainClassNaturality.naturality_apply]
  apply congrArg (Module.CochainClasses.classMap (Cech.complex U P) m)
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (CechCoordinates.topInclusion_naturality U N m hm a) z

variable (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ) (c : ℕ)
  (outgoing : ∀ q, ((CechFunctor.bicomplex U K).d c (c+1)).f q = 0)

theorem topTotalClass_edge (z : (K.X c).obj (op (CechCoordinates.topObject U m hm)))
    (hz : (K.d c (c+1)).app (op (CechCoordinates.topObject U m hm)) z = 0) :
    CechLargeTop.topTotalClass U K m hm c z hz =
      TopRowEdge.map (CechFunctor.bicomplex U K) c outgoing m (topClass U (K.X c) m hm z) := by
  let v : Module.CochainClasses.cycles ((CechFunctor.bicomplex U K).X c) m := topCycle U (K.X c) m hm z
  have hc : CechLargeTop.topTotalCycle U K m hm c z hz =
      TopRowEdge.cycleMap (CechFunctor.bicomplex U K) c outgoing m v := by
    apply Subtype.ext
    rfl
  change Module.CochainClasses.classMap ((CechFunctor.bicomplex U K).total (.up ℕ)) (c+m)
      (CechLargeTop.topTotalCycle U K m hm c z hz) =
    TopRowEdge.map (CechFunctor.bicomplex U K) c outgoing m
      (Module.CochainClasses.classMap ((CechFunctor.bicomplex U K).X c) m v)
  exact (congrArg (Module.CochainClasses.classMap ((CechFunctor.bicomplex U K).total (.up ℕ)) (c+m)) hc).trans
    (TopRowEdge.map_class (CechFunctor.bicomplex U K) c outgoing m v).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopClass
