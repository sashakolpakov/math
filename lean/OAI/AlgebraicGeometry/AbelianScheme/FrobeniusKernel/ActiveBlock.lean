import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtalePoints

/-! # Active Block -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveBlock.Construction

noncomputable section

/-!
Bundle the original source and target active blocks and the proved
point-bijective map. Plane transport is constructed from this source
data. Bundling keeps concrete integral-family expressions out of the
generic character-label inference.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]

structure ActiveBlockTransportData where
  source : Grp (Over (Spec (.of k)))
  target : Grp (Over (Spec (.of k)))
  sourceSplitting : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q source
  targetSplitting : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q target
  map : source ⟶ target
  pointsBijective : Function.Bijective ((yonedaGrp.map map).app (op (Over.mk (𝟙 _))))

namespace ActiveBlockTransportData

variable {k q} (D : ActiveBlockTransportData k q)

def planeIso : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ≅ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q :=
  ActiveEtalePoints.Construction.activeEtaleIsoOfPoints k q D.sourceSplitting D.targetSplitting D.map D.pointsBijective

theorem planeIso_inclusion :
    D.planeIso.hom ≫ ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q D.targetSplitting =
      ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q D.sourceSplitting ≫ D.map := by
  exact (congrArg (fun z => z ≫ ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q D.targetSplitting)
    (ActiveEtalePoints.Construction.activeEtaleIsoOfPoints_hom k q D.sourceSplitting D.targetSplitting D.map D.pointsBijective)).trans
      (ActiveEtaleTransport.Construction.activeEtaleMap_inclusion k q D.sourceSplitting D.targetSplitting D.map)

end ActiveBlockTransportData

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveBlock.Construction
