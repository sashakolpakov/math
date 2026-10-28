import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryKernelImages

/-! # Image Membership -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Turn the computed generic image into exact pointwise membership
in the constructed integral kernel, in the original ambient source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

section

universe u

theorem Kernel.ImageMembership.sourceKernel_image_membership {S : Scheme.{u}} {A T M E : Over S} {F V : Type}
    (s : M ⊗ E ≅ A) (m : (T ⟶ M) ≃ F) (v : (T ⟶ E) ≃ V)
    (K : Intrinsic.Neighbors.KernelPresentation A) (a : T ⟶ A) :
    GenericParameters.blockCoordinates m v (a ≫ s.inv) ∈ SourceKernelImages.sourceKernelPointImage s m v K ↔
      ∃ b : T ⟶ K.carrier, b ≫ K.inclusion = a := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (cancel_mono s.inv).mp ((GenericParameters.blockCoordinates m v).injective hb)⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩

end

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.ImageMembership

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (q : ℕ) [Fact q.Prime] (A : Grp (Over (Spec (.of R))))
  (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_generic_membership
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) (a : Evaluated.Sections.Lifts.genericTest R L ⟶ A.X) :
    let s : C.identity.X ⊗
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X ≅ A.X :=
        (Grp.forget _).mapIso C.split
    GenericParameters.blockCoordinates (C.coordinates.toEquiv.trans Multiplicative.toAdd)
      ((Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative (Fin 2 → ZMod q))).toEquiv.trans Multiplicative.toAdd)
      (a ≫ s.inv) ∈ J ↔
      ∃ b : Evaluated.Sections.Lifts.genericTest R L ⟶ (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel
        (R := R) (L := L) (q := q) (A := A) C J).carrier,
        b ≫ (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel (R := R) (L := L) (q := q) (A := A) C J).inclusion = a := by
  dsimp only
  change _ ∈ (J : Set ((Fin 2 → ZMod q) × ZMod q)) ↔ _
  rw [← OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_generic_image R L q A C J]
  exact Kernel.ImageMembership.sourceKernel_image_membership _ _ _ _ a

variable [IsCommMonObj A.X] (hk : ∀ a : Evaluated.Sections.Lifts.genericTest R L ⟶ A.X, a ^ q = 1)

omit [IsFractionRing R L] in
theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.linearCoordinates_apply (a : Evaluated.Sections.Lifts.genericTest R L ⟶ A.X) :
    letI := GenericPointCoordinates.Lifts.genericPointModule R L q A.X hk
    OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.linearCoordinates (R := R) (L := L) (q := q) (A := A) C hk (Additive.ofMul a) =
      GenericParameters.blockCoordinates (C.coordinates.toEquiv.trans Multiplicative.toAdd)
        ((Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative (Fin 2 → ZMod q))).toEquiv.trans Multiplicative.toAdd)
        (a ≫ ((Grp.forget _).mapIso C.split).inv) := rfl

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_linear_membership
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) (a : Evaluated.Sections.Lifts.genericTest R L ⟶ A.X) :
    letI := GenericPointCoordinates.Lifts.genericPointModule R L q A.X hk
    OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.linearCoordinates (R := R) (L := L) (q := q) (A := A) C hk (Additive.ofMul a) ∈ J ↔
      ∃ b : Evaluated.Sections.Lifts.genericTest R L ⟶ (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel
        (R := R) (L := L) (q := q) (A := A) C J).carrier,
        b ≫ (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel (R := R) (L := L) (q := q) (A := A) C J).inclusion = a := by
  let := GenericPointCoordinates.Lifts.genericPointModule R L q A.X hk
  rw [OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.linearCoordinates_apply R L q A C hk]
  exact OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_generic_membership R L q A C J a

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
