import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateLinear
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SourceKernelImages

/-! # Ordinary Kernel Images -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The constructed ordinary model's integral kernels have exactly
the indexed generic subspace as their image in the original source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SourceKernelImages

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (q : ℕ) [Fact q.Prime] (A : Grp (Over (Spec (.of R))))
  (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_generic_image
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) :
    let s : C.identity.X ⊗
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X ≅ A.X :=
        (Grp.forget _).mapIso C.split
    SourceKernelImages.sourceKernelPointImage s (C.coordinates.toEquiv.trans Multiplicative.toAdd)
      ((Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative (Fin 2 → ZMod q))).toEquiv.trans Multiplicative.toAdd)
      (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel (R := R) (L := L) (q := q) (A := A) C J).toKernelPresentation =
        (J : Set ((Fin 2 → ZMod q) × ZMod q)) := by
  let : IsFinite C.identity.X.hom := C.finite
  let : Flat C.identity.X.hom := C.flat
  let : LocallyOfFinitePresentation C.identity.X.hom := C.finitePresentation
  let s : C.identity.X ⊗
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X ≅ A.X :=
    (Grp.forget _).mapIso C.split
  have : IsMonHom s.hom := C.split.hom.hom.isMonHom_hom
  exact SourceKernelImages.Lifts.evaluatedFiniteFlatKernel_generic_image R L C.coordinates s J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
